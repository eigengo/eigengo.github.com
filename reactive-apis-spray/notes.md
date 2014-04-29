#Hello, world
We start with the ``HelloWorld`` app and the ``HelloWorldService``, which show the low-level Spray API. We begin with

```scala
class HelloWorldService extends Actor {
  def receive: Receive = {
    case r: HttpRequest =>
      sender ! HttpResponse(entity = HttpEntity("Hello, world"))
    // -------------------------------------------------
    case _: Http.Connected =>
      sender ! Http.Register(self)
    // -------------------------------------------------
  }
}
```

Notice the ``_: Http.Connected`` and the matching reply to register ``self`` as the actor that will handle the requests on this connection. We have implemented the _singleton_ handler pattern.

To see it run, we must create the ``HelloWorld`` app.

```scala
object HelloWorld extends App {
  val system = ActorSystem()
  val service = system.actorOf(Props[HelloWorldService])

  IO(Http)(system) ! Http.Bind(service, "0.0.0.0", port = 8080)

  Console.readLine()
  system.shutdown()
}
```

#Testing Hello, world
Because the ``HelloWorldService`` is an ``Actor``, one can use the [Akka TestKit](http://http://doc.akka.io/docs/akka/snapshot/scala/testing.html) to check that it works as expected. And so, we write our test:

```scala
class HelloWorldServiceSpec extends TestKit(ActorSystem())
  with SpecificationLike with ImplicitSender {

  val service = TestActorRef[HelloWorldService]

  "Any request" should {
    "Reply with Hello, world" in {
      service ! HttpRequest()
      expectMsgType[HttpResponse].entity mustEqual HttpEntity("Hello, world")
    }
  }

}
```

---

#Too low-level
The code in ``HelloWorldService`` is jolly reactive, but one would find it hard to construct a complex API by handling the incoming ``HttpRequest`` messages. Spray provides a convenient DSL that can be used to construct the ``Receive`` partial function, which will make it trivial to plug into some low-level ``Actor`` implementation. The author will showcase some of the features of the Spray DSL; focusing in particular on their design motivation.

###DSL Hello, world
We begin by a ``Route`` that implements the same _Hello, world_ behaviour. We will package the route into a ``trait`` so that we can assemble our system's overall API _per partes_.

```scala
trait DemoRoute extends Directives {

  val demoRoute: Route =
    get {
      complete {
        "Hello, world"
      }
    }
}
```

###The service
Having a ``Route`` is a good start, but we must wire it into an implementation of ``Actor``, just like we did earlier. One can extend Spray's ``HttpServiceActor`` and implement the ``receive`` function by applying the ``runRoute`` from ``HttpServiceActor`` to turn the ``Route`` into the ``Receive`` partial function.

```scala
class MainService(route: Route) extends HttpServiceActor {
  def receive: Receive = runRoute(route)
}
```

As a starting point, we will also create the ``MainService`` companion object that will mix in the traits that represent our API.

```scala
object MainService extends DemoRoute {

  val route: Route = demoRoute

}
```

Finally, we bind the ``MainService`` to all local addresses on port 8080, just like we've done earlier.


```scala
object Main extends App {
  val system = ActorSystem()

  val service = system.actorOf(Props(new MainService(MainService.route)))

  IO(Http)(system) ! Http.Bind(service, "0.0.0.0", port = 8080)

  Console.readLine()
  system.shutdown()
}

```

###It gets better
Leaving our the rainbows, ponies & unicorns for some other talk; using Spray's DSL allows us to further simplify our tests. Instead of having to deal with the raw ``HttpRequest``s and ``HttpResponse``s, we can use yet another convenient DSL thusly:

```scala
class DemoRouteSpec extends Specification with Specs2RouteTest with DemoRoute {

  "Any request" should {
    "Reply with Hello, World" in {
      Get() ~> demoRoute ~> check {
        responseAs[String] mustEqual "Hello, world"
      }
    }
  }

}
```

###Onwards
Alas! the ``DemoRoute`` is still very far away from a rich API that we're hoping to construct. Let's try out some of the other directives that Spray comes with out of the box. We'll start with matching URLs. We will handle URL in that match these "shapes":

* ``customer/{id}``, where ``{id}`` is an integer
* ``customer?id={id}``, where ``{id}`` is an integer
* ``colour?r={r}&g={g}&b={b}``, where ``{r}``, ``{g}`` and ``{b}`` are integers

Notice how the inner route changes depending on the specified ``PathMatcher``. In case of ``IntNumber``, the inner path must be ``Int => Route``; in case of ``('r.as[Int], 'g.as[Int], 'b.as[Int])``, it must be ``(Int, Int, Int) => Route``.

```scala
trait UrlMatchingRoute extends Directives {

  val urlMatchingRoute =
    get {
      path("customer" / IntNumber) { id =>
        complete {
          s"Customer with id $id"
        }
      } ~
        path("customer") {
          parameter('id.as[Int]) { id =>
            complete {
              s"Customer with id $id"
            }
          }
        }
      path("colour") {
        parameters(('r.as[Int], 'g.as[Int], 'b.as[Int])) { (r, g, b) =>
          complete {
            <html>
              <body>
                <p>{r}</p>
                <p>{g}</p>
                <p>{b}</p>
              </body>
            </html>
          }
        }
      }
    }

}
```

We can now go ahead and remove the _any request goes_ route in the ``MainService`` and mix in the ``UrlMatchingRoute`` to the ``MainService.route``:

```scala
object MainService extends UrlMatchingRoute {

  val route: Route = urlMatchingRoute

}
```

Observe! One can request ``/customer/1``, ``/customer/10000``, ``/customer?id=42``, ``/colour?r=1&g=2&b=3``, and all is working. Making an invalid request (say forgetting the query parameter, or using a non-integer) produces a reasonable error.

---

But consider the colours: request like ``/colour?r=1&g=1&b=1024`` is valid, but the the colour is not. Moreover, it would be ever-so-nice to have a type that represents a colour, not just three integers. Under the hood, the Spray matchers use [Shapeless](https://github.com/milessabin/shapeless); and so we can take advantage of an isomorphism between tuples and case classes. So, we can remove the ugly ``(r, g, b)`` and replace it with

```scala
  case class Colour(r: Int, g: Int, b: Int) {
    require(r >= 0 && r <= 255)
    require(g >= 0 && g <= 255)
    require(b >= 0 && b <= 255)
  }
```

Ha! And include the ``require`` validation. Now, to modify our ``path("colour")`` matcher, one has to simply require the right type. (Oh, and because we don't want to wear out our keyboards by having to prefix the ``r``, ``g`` and ``b`` references by ``colour.``, we simply add ``import colour._``. Neat!).


```scala
...
  parameters(('r.as[Int], 'g.as[Int], 'b.as[Int])).as(Colour) { colour: Colour =>
    import colour._
    complete {
      ...
    }
```

###More matchers
Just for good measure, I will add an example that shows matching on HTTP headers and cookies. Observe!

```scala
trait HeadersMatchingRoute extends Directives {

  val headersMatchingRoute =
    get {
      path("browser") {
        headerValueByName("User-Agent") { userAgent =>
          complete {
            s"Client is $userAgent"
          }
        }
      }
    }

}
```

and

```scala
trait CookiesMatchingRoute extends Directives {

  val cookiesMatchingRoute =
    get {
      path("cookie") {
        cookie("spray") { spray =>
          complete {
            s"The value is $spray"
          }
        }
      }
    } ~
    post {
      path("cookie") {
        setCookie(HttpCookie("spray", "SGVsbG8sIHdvcmxkCg==", httpOnly = true)) {
          complete {
            "Cookie created"
          }
        }
      }
    }
}
```

Now, how do we add the newly constructed ``cookiesMatchingRoute`` and ``headersMatchingRoute`` to our ``MainService.route``? Well, notice that we have concatenated our routes with ``~``, and there's nothing stopping us from doing the same in the ``MainService.route``:

```scala
object MainService 
  extends UrlMatchingRoute 
  with HeadersMatchingRoute 
  with CookiesMatchingRoute {

  val route: Route = 
    urlMatchingRoute ~ 
    headersMatchingRoute ~ 
    cookiesMatchingRoute

}
```

#Let's build a real thing
So, we've seen what the Spray DSL can do, and how easy it is to wire things together. Unfortunately, our responses leave _a lot_ to be desired. _Hello, world_? ``<html><body><p>1</p>...</body></html>`` is not what one would call a complex API.

Let's build big data analytics of tweets. We have 30 minutes to do it. What could possibly go wrong?

So, we want to build API that when we post a query (``POST`` to ``tweets/{query}``, where ``{}), it forwards it to the Twitter API, and then streams the analytics results as the tweets arrive from Twitter. Naturally, it should all be non-blocking. Oh, and since we're in the _big data_ business, let's just count things. (What, you expected any significant mathematics?)

The components we'll need are the ``TwitterReaderActor`` that talks to the real Twitter API and performs analytics on the tweets as they arrive. We will also need to use it in a ``TweetAnalysisRoute`` trait that will expose a ``Route`` that we can then add to our API. Easy. 

###TweetReaderActor
Let's start by exploring Spray client, which allows us to construct reactive API clients. Before we jump into the code, let's all take a moment to remember that Twitter uses pesky OAuth to authorise the requests applications send to it. Through the power of abstraction, we can leave out the hard work for a few minutes later!

```scala
trait TwitterAuthorization {
  def authorize: HttpRequest => HttpRequest
}

object TweetReaderActor {
  val twitterUri = Uri("https://stream.twitter.com/1.1/statuses/filter.json")
}

class TweetReaderActor(uri: Uri, receiver: ActorRef) extends Actor with TweetMarshaller {
  this: TwitterAuthorization =>
  
  def receive: Receive = ???
}
```

All that we have to do is to implement the ``receive`` function. When we receive the query (a message of type ``String``), we will fire off the streaming request to twitter, specifying ourselves as the receivers of the incoming HTTP message chunks. As each chunk arrives, we unmarshal its JSON, pass it on to be analysed, and send the result to the ``receiver``.

```scala
class TweetReaderActor(uri: Uri, receiver: ActorRef) extends Actor with TweetMarshaller {
  this: TwitterAuthorization =>
  val io = IO(Http)(context.system)
  val sentimentAnalysis = new SentimentAnalysis with CSVLoadedSentimentSets

  def receive: Receive = {
    case query: String =>
      val post = HttpEntity(ContentType(MediaTypes.`application/x-www-form-urlencoded`), s"track=$query")
      val rq = HttpRequest(HttpMethods.POST, uri = uri, entity = post) ~> authorize
      sendTo(io).withResponsesReceivedBy(self)(rq)
    case ChunkedResponseStart(_) =>
    case MessageChunk(entity, _) =>
      TweetUnmarshaller(entity) match {
        case Right(tweet) => receiver ! sentimentAnalysis.onTweet(tweet)
        case _            =>
      }
    case _ =>
  }
}
```

(I happen to have implemented the ``SentimentAnalysis`` class already. I leave its destruction to the curious readers.)

Unfortunately, our abstraction is going to start biting pretty soon; when we come to make instances of the ``TweetReaderActor``. And so, we move to implement the ``OAuthTwitterAuthorization``:

```scala
trait OAuthTwitterAuthorization extends TwitterAuthorization {
  import OAuth._
  val home = System.getProperty("user.home")
  val lines = Source.fromFile(s"$home/.twitter/phillyete2014").getLines().toList

  val consumer = Consumer(lines(0), lines(1))
  val token = Token(lines(2), lines(3))

  val authorize: HttpRequest => HttpRequest = oAuthAuthorizer(consumer, token)
}
```

Jolly good. We can now construct ``new TweetReaderActor(TweetReaderActor.twitterUri, receiver) with OAuthTwitterAuthorization`` and all will be well. The last piece of the puzzle is therefore the ``TweetAnalysisRoute``.

###TweetAnalysisRoute
Because everything is loosely-coupled, we can start with the ``TweetAnalysisRoute``. We begin with a simple

```scala
trait TweetAnalysisRoute extends Directives {

  val tweetAnalysisRoute: Route =
    post {
      path("tweets" / Segment)(sendTweetAnalysis)
    }

}
```

So, when we have a ``POST`` request to ``tweets/{query}``, Spray completes it by running the ``sendTweetAnalysis`` function. So, the "shape" of the ``sendTweetAnalysis`` has to match the route that Spray is expecting. In this case, it has to be ``String => RequestContext => ()``. Easy.


```scala
trait TweetAnalysisRoute extends Directives {

  val tweetAnalysisRoute: Route =
    post {
      path("tweets" / Segment)(sendTweetAnalysis)
    }

  def sendTweetAnalysis(query: String)(ctx: RequestContext): Unit = {
    // magic
  }

}
```

Unfortunately, ``//magic`` is only an experimental feature in Scala 3.0, we must implement an actor that will start off the query to Twitter, and as the analysed results arrive, send them to the client that made the request. So, in our ``sendTweetAnalysis`` function, we'll be creating ``Actor``s, so we need ``ActorRefFactory``.

```scala
trait TweetAnalysisRoute extends Directives {

  def tweetAnalysisRoute(implicit actorRefFactory: ActorRefFactory): Route =
    post {
      path("tweets" / Segment)(sendTweetAnalysis)
    }

  def sendTweetAnalysis(query: String)(ctx: RequestContext)(implicit actorRefFactory: ActorRefFactory): Unit = {
    actorRefFactory.actorOf(Props(new TweetAnalysisStreamingActor(query, ctx.responder)))
  }

  class TweetAnalysisStreamingActor(query: String, responder: ActorRef) extends Actor {
    // magic
  }
}
```

Now, this seems quite reasonable. When we receive the request, we pull out the query, and then construct an actor that will keep sending portions of the response to the ``RequestContext.receiver``, which represents the connected client. We can now turn our eyes on the implementation of the ``TweetAnalysisStreamingActor``.

Upon creation, it is going to construct the ``TweetReaderActor``


```scala
trait TweetAnalysisRoute extends Directives {
  ...

  class TweetAnalysisStreamingActor(query: String, responder: ActorRef) extends Actor {
    import ContentTypes._
    val reader = context.actorOf(
      Props(new TweetReaderActor(TweetReaderActor.twitterUri, self)
                  with OAuthTwitterAuthorization))
    val responseStart = HttpResponse(entity = HttpEntity(`application/json`, "{}"))
    responder ! ChunkedResponseStart(responseStart).withAck('start)

    def receive: Receive = {
      case 'start =>
        reader ! query
      case _: Http.ConnectionClosed =>
        responder ! ChunkedMessageEnd
        context.stop(reader)
        context.stop(self)
      case analysed: Map[String, Map[String, Int]] =>
        val items = analysed.map { case (category, elements) => category ->
          JsArray(elements.map {
            case (k, v) => JsObject("name" -> JsString(k), "value" -> JsNumber(v))
          }.toList)
        }
        val body = CompactPrinter(JsObject(items))
        responder ! MessageChunk(body)
    }
  }

}
```

So this is looking really good! We can receive the request, construct the actor that will talk to the Twitter API, do its _big data_ business, and we then turn its output into suitable JSON output. Now, before we see the glorious results, we might want to consider what happens when, say, a browser running some funky JavaScript makes the request. Any self-respecting browser will check for cross-origin requests. Before we leave the ``TweetAnalysisRoute``, we'll allow all cross-origin requests. (My heart bleeds!)

```scala
trait TweetAnalysisRoute extends Directives {

  ...

  class TweetAnalysisStreamingActor(query: String, responder: ActorRef) extends Actor {
    val allCrossOrigins =
      RawHeader("Access-Control-Allow-Origin", "*") ::
        RawHeader("Access-Control-Allow-Methods", "GET, POST, PUT, DELETE") :: Nil

    import ContentTypes._
    val reader = context.actorOf(Props(new TweetReaderActor(TweetReaderActor.twitterUri, self)
      with OAuthTwitterAuthorization))
    val responseStart = HttpResponse(entity = HttpEntity(`application/json`, "{}"), headers = allCrossOrigins)
    responder ! ChunkedResponseStart(responseStart).withAck('start)

    def receive: Receive = {
      case 'start =>
        reader ! query
      case _: Http.ConnectionClosed =>
        responder ! ChunkedMessageEnd
        context.stop(reader)
        context.stop(self)
      case analysed: Map[String, Map[String, Int]] =>
        val items = analysed.map { case (category, elements) => category ->
          JsArray(elements.map {
            case (k, v) => JsObject("name" -> JsString(k), "value" -> JsNumber(v))
          }.toList)
        }
        val body = CompactPrinter(JsObject(items))
        responder ! MessageChunk(body)
    }
  }

}
```

###MainService
Ah, now before we see it all in its glorious action, we must add it to the ``MainService``. To apply the usual route concatenation approach, we must be able to pass in the ``ActorRefFactory``. And so ``val`` grows up to become a ``def``:

```scala
object MainService 
  extends UrlMatchingRoute 
  with HeadersMatchingRoute 
  with CookiesMatchingRoute 
  with TweetAnalysisRoute {

  def route(arf: ActorRefFactory): Route = 
    urlMatchingRoute ~ 
    headersMatchingRoute ~ 
    cookiesMatchingRoute ~ 
    tweetAnalysisRoute(arf) 

}
```

Arf!

###Try it out
To see it all run, we can try an old friend: ``telnet``.

```bash
$ telnet localhost 8080
Trying ::1...
Connected to localhost.
Escape character is '^]'.
POST /tweets/uk HTTP/1.1
Host: localhost

HTTP/1.1 200 OK
Server: spray-can/1.3.0
Date: Wed, 16 Apr 2014 15:30:22 GMT
Access-Control-Allow-Origin: *
Access-Control-Allow-Methods: GET, POST, PUT, DELETE
Content-Type: application/json; charset=UTF-8
Transfer-Encoding: chunked

2
{}
db
{"counts":[{"name":"positive.gurus","value":1},{"name":"negative.gurus","value":1},{"name":"negative","value":1},{"name":"positive","value":1}],"languages":[{"name":"en","value":1}],"places":[{"name":"None","value":1}]}
db
...
```
Great. What more could our users want?

###Speaking of users
I happen to have prepared an AngularJS application that perverts our lovely JSON on the console into some HTML5 with charts and whatnot... Open ``web/tweets.html``, enter the query into the box and start losing faith in humanity...

#Summary
Head over to [https://github.com/eigengo/phillyete2014](https://github.com/eigengo/phillyete2014) for the source code, to [http://www.cakesolutions.net/teamblogs](http://www.cakesolutions.net/teamblogs) for the blog post.