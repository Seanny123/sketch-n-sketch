//////////////////////////////////////////////////////////////////////

var editor;
var markers = [];
var fontSize = 16;

function initialize() {
  editor = ace.edit("editor");
  editor.$blockScrolling = Infinity;
  editor.setTheme("ace/theme/chrome");
  editor.setFontSize(fontSize);
  editor.getSession().setMode("ace/mode/little");
  editor.setOption("dragEnabled", true); // true by default anyway
  editor.setOption("highlightActiveLine", false);
  editor.setShowPrintMargin(false);
  editor.getSession().setUseSoftTabs(true);
  editor.getSession().setTabSize(2);

  editor.on("input", function() {
      var info = getEditorState();
      app.ports.receiveEditorState.send(info);
  });
  editor.selection.on("changeCursor", function() {
      var info = getEditorState();
      app.ports.receiveEditorState.send(info);
  });

  editor.getSession().on("changeScrollTop", function() {
      var info = getEditorState();
      app.ports.receiveEditorState.send(info);

  });
  editor.getSession().on("changeScrollLeft", function() {
      var info = getEditorState();
      app.ports.receiveEditorState.send(info);
  });

}


//////////////////////////////////////////////////////////////////////
// Ranges (i.e. Highlights)

var Range = ace.require('ace/range').Range

// So we can dynamically add CSS classes, which is needed to style the markers
// Generally only touches the DOM to add new ones if absolutely needed

var style = document.createElement('style');
style.id = "autogenerated_css_classes";
style.type = 'text/css';
document.getElementsByTagName('head')[0].appendChild(style);
var classDict = {};

function makeCSSClass(colorStr) {
    var autogenName = ".autogenerated_class_" + colorStr
    if (!(classDict.hasOwnProperty(autogenName))) {
        style.innerHTML = style.innerHTML
                            + ".ace_marker-layer "
                            + autogenName
                            + " { background-color : " + colorStr+ "; "
                            + "position : absolute; "
                            + "z-index : 2; "
                            + "} ";
        document.getElementById("autogenerated_css_classes").innerHTML = style.innerHTML;
        classDict[autogenName] = true;
    }
    return "autogenerated_class_" + colorStr;
}


//////////////////////////////////////////////////////////////////////
// Demo: Displaying a hover annotation (for entire line)

function setDummyAnnotations() {

  var annots = [
    { row: 0 , text: "Info!" , type: "info" }
  , { row: 1 , text: "Warning!" , type: "warning" }
  , { row: 2 , text: "Error!" , type: "error" }
  ];

  editor.getSession().setAnnotations(annots);
}


//////////////////////////////////////////////////////////////////////
// Demo: A "tooltip" provides info when hovering over the token
// starting at a given row/column
//
// clearTooltips() and addTooltip() are defined in aceTooltips.js

function setDummyTooltips() {
  var typeTooltip = new TokenTooltip(editor, getTooltipText);
  clearTooltips();
  addTooltip(0, 0, "Don't click on me, it hurts.");
  addTooltip(0, 1, "Click on me to rewrite.");
}


//////////////////////////////////////////////////////////////////////
// Display AceCodeBoxInfo from Elm

function display(info) {
  // TODO get resizing working better with dragLayoutWidget
  // editor.resize();
  // reembed(false);

  displayCode(info.code);
  displayCursor(info.codeBoxInfo.cursorPos);
  // editor.selection.clearSelection(); // TODO selections
  displayMarkers(info.codeBoxInfo.highlights);
  displayAnnotations(info.codeBoxInfo.annotations);
  displayTooltips();
}

function displayCode(code) {
  editor.getSession().setValue(code, 0);
}

function displayCursor(cursorPos) {
  editor.moveCursorTo(cursorPos.row, cursorPos.column);
}

function displayMarkers(highlights) {

  // Add the special syntax highlighting for changes and such
  // These are 'markers', see:
  // http://ace.c9.io/#nav=api&api=edit_session
  // ctl+f addMarker
  for (mi in markers) {
      editor.getSession().removeMarker(markers[mi]);
  }
  markers = [];
  for (hi in highlights) {
      hiRange = highlights[hi].range;
      var aceRange = new Range(hiRange.start.row - 1, //Indexing from 1 in Elm?
                               hiRange.start.column - 1,
                               hiRange.end.row - 1,
                               hiRange.end.column - 1);
      var hiClass = makeCSSClass(highlights[hi].color);
      var mid = editor.getSession().addMarker(aceRange,hiClass,"text", false);
      editor.resize();
      markers.push(mid);
  }
  editor.updateSelectionMarkers();
}

function displayAnnotations(annotations) {

  // setDummyAnnotations();

  editor.getSession().clearAnnotations();
  var annots = [];
  for (idx in annotations) {
      console.log("annot: " + annotations[idx].row);
      annots.push(
          { row  : annotations[idx].row
          , text : annotations[idx].text
          , type : annotations[idx].type_
          });
  }
  editor.getSession().setAnnotations(annots);
}

function displayTooltips() {
  // TODO
  // setDummyTooltips();
}


//////////////////////////////////////////////////////////////////////
// Update AceCodeBoxInfo to Send to Elm

function getEditorState() {
  var codeBoxInfo =
    { cursorPos : editor.getCursorPosition()
    , selections : editor.selection.getAllRanges()
    , highlights : [] // TODO
    , annotations : [] // TODO
    , tooltips : [] // TODO
    , fontSize : fontSize
    , lineHeight : editor.renderer.layerConfig.lineHeight
    , characterWidth : editor.renderer.layerConfig.characterWidth
    , offsetLeft: editor.renderer.container.offsetLeft
    , offsetHeight: editor.renderer.container.offsetTop
    , gutterWidth: editor.renderer.gutterWidth
    , firstVisibleRow: editor.renderer.getFirstVisibleRow()
    , lastVisibleRow: editor.renderer.getLastVisibleRow()
    , marginTopOffset: document.getElementsByClassName("ace_content")[0].offsetTop
    , marginLeftOffset: document.getElementsByClassName("ace_content")[0].offsetLeft
    };
  var info =
    { code : editor.getSession().getDocument().getValue()
    , codeBoxInfo : codeBoxInfo
    };
  return info;
}


//////////////////////////////////////////////////////////////////////
// Ports

app.ports.aceCodeBoxCmd.subscribe(function(aceCmd) {
  var message = aceCmd.message;

  if (message == "initializeAndDisplay") {
    initialize();
    display(aceCmd.info);

  } else if (message == "display") {
    display(aceCmd.info);

  } else if (message == "resize") {
    editor.resize();
    display(aceCmd.info);

  } else if (message == "updateFontSize") {
    fontSize = aceCmd.info.codeBoxInfo.fontSize;
    editor.setFontSize(fontSize);
    display(aceCmd.info);

  } else if (message == "changeScroll") {

  } else {
    console.log("[aceCodeBox.js] unexpected message: " + message);
  }

});

// receiveEditorState port is in initialize()
