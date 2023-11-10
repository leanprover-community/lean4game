
const IO = {
  _resolveGetLine: null,
  _resolveRead: null,
  _readPointer: null,
  _nbytes: 0,
  bufferStdIn : "",
  putStrListeners: [],
  listenPutStr(callback) {
    this.putStrListeners.push(callback)
  },
  putStr(str) {
    console.log('PUTSTR' + str)
    str = str.split('\n')[2]
    this.putStrListeners.forEach((listener) => {
      listener(str)
    })
  },
  async getLine() {
    return new Promise((resolve, reject) => {
        this._resolveGetLine = resolve
        this.flushStdIn();
    });
  },
  async read(ptr, nbytes) {
    this._nbytes = nbytes
    this._readPointer = ptr
    return new Promise((resolve, reject) => {
        this._resolveRead = resolve
        this.flushStdIn();
    });
  },
  flushStdIn() {
    if(this._resolveGetLine) {
      var lineBreak = this.bufferStdIn.indexOf("\n")
      if (lineBreak != -1) {
        this._resolveGetLine(stringToNewUTF8(this.bufferStdIn.substring(0,lineBreak+1)))
        this.bufferStdIn = this.bufferStdIn.substring(lineBreak+1)
        this._resolveGetLine = null
      }
    }
    if(this._resolveRead) {
      // console.log(`read: ${this.bufferStdIn}`)
      stringToUTF8(this.bufferStdIn, this._readPointer, this._nbytes);
      this._resolveRead()
      this.bufferStdIn = ""
      this._resolveRead = null
    }
  },
  putLine(data) {
    console.log("Client: ",data)
    const str = data + '\r\n'
    const byteLength = lengthBytesUTF8(str)
    this.bufferStdIn += `Content-Length: ${byteLength}\r\n\r\n` + str
    this.flushStdIn();
  }
}


var input = ""
var i = 0;

function submit (ev) {
ev.preventDefault()
return false;
}

var stdoutBuffer = ""
var stderrBuffer = ""


var Module = {
  "arguments": ["--worker"],
  "preRun": [function() {
    function stdin() {
        if (i < input.length) {
          i++;
          return input.charCodeAt(i);// Return ASCII code of character, or null if no input
        } else {
          return null
        }
    }

    function stdout(asciiCode) {
      stdoutBuffer += String.fromCharCode(asciiCode)
    }

    function stderr(asciiCode) {
      stderrBuffer += String.fromCharCode(asciiCode)
    }

    FS.init(stdin, stdout, stderr);
  }]
};

importScripts("server.js")


onmessage = (ev) => {
  IO.putLine(ev.data)
}

IO.listenPutStr(message => {
  postMessage(message)
})

setInterval(() => {
  if (stdoutBuffer !== "") {
    console.log(stdoutBuffer);
    stdoutBuffer = ""
  }
  if (stderrBuffer !== "") {
    console.error(stderrBuffer);
    stderrBuffer = ""
  }
}, 1000)

setTimeout(() =>{
  Module.ccall('send_message', // name of C function
  'void', // return type
  ['string'], // argument types
  ['Hi there!']); // arguments
},2000)
