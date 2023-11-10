

import { DataCallback, AbstractMessageReader, MessageReader } from 'vscode-jsonrpc/lib/common/messageReader.js';

import { Message } from 'vscode-jsonrpc/lib/common/messages.js';
import { AbstractMessageWriter, MessageWriter } from 'vscode-jsonrpc/lib/common/messageWriter.js';
import { Emitter } from 'vscode-jsonrpc/lib/common/events.js';
import { Disposable, IWebSocket } from 'vscode-ws-jsonrpc/.';

declare var IO: any;

export class WasmWriter implements MessageWriter {
  protected errorCount = 0;
  errorEmitter
  closeEmitter
  constructor(private worker: Worker) {
    this.errorEmitter = new Emitter()
    this.closeEmitter = new Emitter()
}
dispose() {
    this.errorEmitter.dispose();
    this.closeEmitter.dispose();
}
get onError() {
    return this.errorEmitter.event;
}
fireError(error, message, count) {
    this.errorEmitter.fire([this.asError(error), message, count]);
}
get onClose() {
    return this.closeEmitter.event;
}
fireClose() {
    this.closeEmitter.fire(undefined);
}
asError(error) {
    if (error instanceof Error) {
        return error;
    }
    else {
        return new Error(`Writer received error. Reason: ${error.message}`);
    }
}

  end(): void {
  }

  async write(msg: Message): Promise<void> {
      try {
          const content = JSON.stringify(msg);
          this.worker.postMessage(content)
      } catch (e) {
          this.errorCount++;
          this.fireError(e, msg, this.errorCount);
      }
  }
}


export class WasmReader implements MessageReader {
  protected state: 'initial' | 'listening' | 'closed' = 'initial';
  protected callback: DataCallback | undefined;
  protected readonly events: { message?: any, error?: any }[] = [];

  constructor(private worker: Worker) {
    this.worker.onmessage = (ev) => {
      this.readMessage(ev.data)
    }
      // this.socket.onMessage(message =>
      //     this.readMessage(message)
      // );
      // this.socket.onError(error =>
      //     this.fireError(error)
      // );
      // this.socket.onClose((code, reason) => {
      //     if (code !== 1000) {
      //         const error: Error = {
      //             name: '' + code,
      //             message: `Error during socket reconnect: code = ${code}, reason = ${reason}`
      //         };
      //         this.fireError(error);
      //     }
      //     this.fireClose();
      // });
    this.errorEmitter = new Emitter()
    this.closeEmitter = new Emitter()
    this.partialMessageEmitter = new Emitter()
  }

  protected errorCount = 0;
  errorEmitter
  closeEmitter
  partialMessageEmitter

dispose() {
    this.errorEmitter.dispose();
    this.closeEmitter.dispose();
}
get onError() {
    return this.errorEmitter.event;
}
get onClose() {
    return this.closeEmitter.event;
}
get onPartialMessage() {
    return this.partialMessageEmitter.event;
}
firePartialMessage(info) {
    this.partialMessageEmitter.fire(info);
}
asError(error) {
    if (error instanceof Error) {
        return error;
    }
    else {
        return new Error(`Reader received error. Reason: ${error.message ? error.message : 'unknown'}`);
    }
}

  listen(callback: DataCallback): Disposable {
      if (this.state === 'initial') {
          this.state = 'listening';
          this.callback = callback;
          while (this.events.length !== 0) {
              const event = this.events.pop()!;
              if (event.message) {
                  this.readMessage(event.message);
              } else if (event.error) {
                  this.fireError(event.error);
              } else {
                  this.fireClose();
              }
          }
      }
      return {
          dispose: () => {
              if (this.callback === callback) {
                  this.callback = undefined;
              }
          }
      };
  }

  protected readMessage(message: any): void {
      if (this.state === 'initial') {
          this.events.splice(0, 0, { message });
      } else if (this.state === 'listening') {
          try {
              const data = JSON.parse(message);
              this.callback!(data);
          } catch (err) {
              const error: Error = {
                  name: '' + 400,
                  message: `Error during message parsing, reason = ${typeof err === 'object' ? (err as any).message : 'unknown'}`
              };
              this.fireError(error);
          }
      }
  }

  protected fireError(error: any): void {
      if (this.state === 'initial') {
          this.events.splice(0, 0, { error });
      } else if (this.state === 'listening') {

    this.errorEmitter.fire(this.asError(error));
      }
  }

  protected fireClose(): void {
      if (this.state === 'initial') {
          this.events.splice(0, 0, {});
      } else if (this.state === 'listening') {
        this.closeEmitter.fire(undefined);
      }
      this.state = 'closed';
  }
}
export class WebSocketMessageWriter implements MessageWriter {
    protected errorCount = 0;
    errorEmitter
    closeEmitter

    constructor(protected readonly socket: IWebSocket) {
        this.errorEmitter = new Emitter();
        this.closeEmitter = new Emitter();
    }
    dispose() {
        this.errorEmitter.dispose();
        this.closeEmitter.dispose();
    }
    get onError() {
        return this.errorEmitter.event;
    }
    fireError(error, message, count) {
        this.errorEmitter.fire([this.asError(error), message, count]);
    }
    get onClose() {
        return this.closeEmitter.event;
    }
    fireClose() {
        this.closeEmitter.fire(undefined);
    }
    asError(error) {
        if (error instanceof Error) {
            return error;
        }
        else {
            return new Error(`Writer received error. Reason: ${(error.message) ? error.message : 'unknown'}`);
        }
    }
    end(): void {
    }

    async write(msg: Message): Promise<void> {
        console.log("WRITE",msg)
        try {
            const content = JSON.stringify(msg);
            this.socket.send(content);
        } catch (e) {
            this.errorCount++;
            this.fireError(e, msg, this.errorCount);
        }
    }
}



export class WebSocketMessageReader implements MessageReader {
    protected state: 'initial' | 'listening' | 'closed' = 'initial';
    protected callback: DataCallback | undefined;
    protected readonly events: { message?: any, error?: any }[] = [];
    errorEmitter
    closeEmitter
    partialMessageEmitter

    constructor(protected readonly socket: IWebSocket) {
        this.errorEmitter = new Emitter();
        this.closeEmitter = new Emitter();
        this.partialMessageEmitter = new Emitter();
        this.socket.onMessage(message =>{
            console.log("READ", message)
            this.readMessage(message)
        });
        this.socket.onError(error =>
            this.fireError(error)
        );
        this.socket.onClose((code, reason) => {
            if (code !== 1000) {
                const error: Error = {
                    name: '' + code,
                    message: `Error during socket reconnect: code = ${code}, reason = ${reason}`
                };
                this.fireError(error);
            }
            this.fireClose();
        });
    }
    dispose() {
        this.errorEmitter.dispose();
        this.closeEmitter.dispose();
    }
    get onError() {
        return this.errorEmitter.event;
    }
    get onClose() {
        return this.closeEmitter.event;
    }
    get onPartialMessage() {
        return this.partialMessageEmitter.event;
    }
    firePartialMessage(info) {
        this.partialMessageEmitter.fire(info);
    }
    asError(error) {
        if (error instanceof Error) {
            return error;
        }
        else {
            return new Error(`Reader received error. Reason: ${(error.message) ? error.message : 'unknown'}`);
        }
    }

    listen(callback: DataCallback): Disposable {
        if (this.state === 'initial') {
            this.state = 'listening';
            this.callback = callback;
            while (this.events.length !== 0) {
                const event = this.events.pop()!;
                if (event.message) {
                    this.readMessage(event.message);
                } else if (event.error) {
                    this.fireError(event.error);
                } else {
                    this.fireClose();
                }
            }
        }
        return {
            dispose: () => {
                if (this.callback === callback) {
                    this.callback = undefined;
                }
            }
        };
    }

    protected readMessage(message: any): void {
        if (this.state === 'initial') {
            this.events.splice(0, 0, { message });
        } else if (this.state === 'listening') {
            try {
                const data = JSON.parse(message);
                this.callback!(data);
            } catch (err) {
                const error: Error = {
                    name: '' + 400,
                    message: `Error during message parsing, reason = ${typeof err === 'object' ? (err as any).message : 'unknown'}`
                };
                this.fireError(error);
            }
        }
    }

    protected fireError(error: any): void {
        if (this.state === 'initial') {
            this.events.splice(0, 0, { error });
        } else if (this.state === 'listening') {
            this.errorEmitter.fire(this.asError(error));
        }
    }

    protected fireClose(): void {
        if (this.state === 'initial') {
            this.events.splice(0, 0, {});
        } else if (this.state === 'listening') {
            this.closeEmitter.fire(undefined);
        }
        this.state = 'closed';
    }
}
