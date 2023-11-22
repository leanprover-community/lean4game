
var stderrBuffer = ""
var messageBuffer = []
var initialized = false;

var headerMode = true;
var header="";
var re = /Content-Length: (\d+)\r\n/i;
var contentLength = 0;
var content = []
var utf8decoder = new TextDecoder();


function flushMessageBuffer(){
  if (initialized) {
    while(messageBuffer.length > 0) {
      var msg = messageBuffer.shift();
      Module.ccall('send_message', 'void', ['string'], [msg]);
    }
  }
}

var Module = {
  "arguments": ["--worker"],
  "preRun": [function() {
    function stdin() {
      return null;
    }

    function stdout(asciiCode) {
      if (headerMode) {
        header += String.fromCharCode(asciiCode)
        if (header.endsWith('\r\n\r\n')) {
          const found = header.match(re)
          if (found == null) { console.error(`Invalid header: ${header}`) }
          contentLength = parseInt(found[1])
          content = []
          headerMode = false
        }
      } else {
        content.push(asciiCode)
        if (content.length == contentLength) {
          const message = utf8decoder.decode(new Uint8Array(content))
          console.log(`Server: ${message}`)
          postMessage(message);
          headerMode = true
          header = ''
        }
      }
    }

    function stderr(asciiCode) {
      stderrBuffer += String.fromCharCode(asciiCode)
    }

    FS.init(stdin, stdout, stderr);
  }],
  "noInitialRun": true,
  "onRuntimeInitialized": () => {
    Module.ccall('main', 'void', [], []);
    initialized = true;
    if (stderrBuffer !== "") {
      console.log(stderrBuffer);
      stderrBuffer = ""
    }
    flushMessageBuffer();
  }
};

importScripts("server.js")



onmessage = (ev) => {
  console.log(`Client: ${ev.data}`)
  messageBuffer.push(ev.data);
  flushMessageBuffer();
}

setInterval(() => {
  if (stderrBuffer !== "") {
    console.log(stderrBuffer);
    stderrBuffer = ""
  }
}, 1000)

setTimeout(() =>{

},2000)
