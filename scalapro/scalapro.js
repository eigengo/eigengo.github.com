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
    index: 0, // current cursor position
    speed: 2, // speed of the Typer
    file: "", //file, must be setted
    init: function () {// inizialize Hacker Typer
        accessCountimer = setInterval(function () { scalapro.updLstChr(); }, 500); // inizialize timer for blinking cursor
        $.get(scalapro.file, function (data) {// get the text file
            scalapro.text = data;// save the textfile in scalapro.text
        });
    },

    content: function () {
        return $("#console").html();// get console content
    },

    write: function (str) {// append to console content
        var block = $("#console");
        block.append(str);
        hljs.highlightBlock(block);
        return false;
    },

    addText: function (key) {//Main function to add the code
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
            var cont = scalapro.content(); // get the console content
            if (cont.substring(cont.length - 1, cont.length) == "|") // if the last char is the blinking cursor
                $("#console").html($("#console").html().substring(0, cont.length - 1)); // remove it before adding the text
            if (key.keyCode != 8) { // if key is not backspace
                scalapro.index += scalapro.speed;	// add to the index the speed
            } else {
                if (scalapro.index > 0) // else if index is not less than 0 
                    scalapro.index -= scalapro.speed;//	remove speed for deleting text
            }
            var text = $("<div/>").text(scalapro.text.substring(0, scalapro.index)).html();// parse the text for stripping html enities
            var rtn = new RegExp("\n", "g"); // newline regex
            var rts = new RegExp("\\s", "g"); // whitespace regex
            var rtt = new RegExp("\\t", "g"); // tab regex
            $("#console").html(text.replace(rtn, "<br/>").replace(rtt, "&nbsp;&nbsp;&nbsp;&nbsp;").replace(rts, "&nbsp;"));// replace newline chars with br, tabs with 4 space and blanks with an html blank
            window.scrollBy(0, 50); // scroll to make sure bottom is always visible
        }
        if (key.preventDefault && key.keyCode != 122) { // prevent F11(fullscreen) from being blocked
            key.preventDefault()
        };
        if (key.keyCode != 122) { // otherway prevent keys default behavior
            key.returnValue = false;
        }
    },

    updLstChr: function () { // blinking cursor
        var cont = this.content(); // get console 
        if (cont.substring(cont.length - 1, cont.length) == "|") // if last char is the cursor
            $("#console").html($("#console").html().substring(0, cont.length - 1)); // remove it
        else
            this.write("|"); // else write it
    }
}