$(
	function () {
	    $(document).keydown(
			function (event) {
			    scalapro.addText(event); 
			}
		);
	}
);

var scalapro = {
    text: null,
    index: 0,
    file: "",

    init: function () {// inizialize Hacker Typer
        accessCountimer = setInterval(function () { scalapro.updLstChr(); }, 500); 
        $.get(scalapro.file, function (data) { 
            scalapro.text = data; 
            var markup = hljs.highlight("scala", "", true).value;
            $("#console").html(markup);
        });
    },

    speed: function() {
        return Math.ceil(Math.random() * 10);
    },

    content: function () {
        return $("#console").html();// get console content
    },

    write: function (str) {// append to console content
        var block = $("#container");
        $("#console").append(str);
        //hljs.highlightBlock(block);
        return false;
    },

    addText: function(key) {
        if (scalapro.text) {
            if (key.keyCode != 8) { // if key is not backspace
                scalapro.index += scalapro.speed();
            } else {
                if (scalapro.index > 0) // else if index is not less than 0 
                    scalapro.index -= scalapro.speed();// remove speed for deleting text
            }

            var text = scalapro.text.substring(0, scalapro.index);
            var markup = hljs.highlight("scala", text, true).value;
            $("#console").html(markup);
            window.scrollBy(0, 50); // scroll to make sure bottom is always visible
        }
        if (key.preventDefault && key.keyCode != 122) { // prevent F11(fullscreen) from being blocked
            key.preventDefault()
        };
        if (key.keyCode != 122) { // otherway prevent keys default behavior
            key.returnValue = false;
        }

    },

    addTextx: function (key) {//Main function to add the code
        if (key.keyCode == 18) {// key 18 = alt key
            scalapro.accessCount++; //increase counter 
            if (scalapro.accessCount >= 3) {// if it's presed 3 times
                scalapro.makeAccess(); // make access popup
            }
        } else if (key.keyCode == 20) {// key 20 = caps lock
            scalapro.deniedCount++; // increase counter
            if (scalapro.deniedCount >= 3) { // if it's pressed 3 times
                scalapro.makeDenied(); // make denied popup
            }
        } else if (key.keyCode == 27) { // key 27 = esc key
            scalapro.hidepop(); // hide all popups
        } else if (scalapro.text) { // otherway if text is loaded
        }
        if (key.preventDefault && key.keyCode != 122) { // prevent F11(fullscreen) from being blocked
            key.preventDefault()
        };
        if (key.keyCode != 122) { // otherway prevent keys default behavior
            key.returnValue = false;
        }
    },

    updLstChr: function () {
        var cont = this.content();
        if (cont.substring(cont.length - 1, cont.length) == "|")
            $("#console").html($("#console").html().substring(0, cont.length - 1)); 
        else
            this.write("|"); 
    }
}