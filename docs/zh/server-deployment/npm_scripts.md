## NPM 脚本

* `npm start`：以开发模式启动项目。当客户端文件发生更改时，浏览器将自动重新加载。当 lean 文件发生更改时，Lean 服务器将被重新编译和重启。此时 Lean 服务器的启动将不依赖容器。客户端和服务器分别使用脚本 `npm run start:client` 和 `npm run start:server` 启动，并通过 `http://localhost:3000` 访问项目。在内部，到 `ws://localhost:3000/websockets` 的 websocket 请求将被转发到运行在端口 `8080` 上的 Lean 服务器。

* `npm run build`：以生产模式构建项目。对于客户端，所有文件将被编译到 `client/dist` 中。对于服务器端，该命令将设置一个包含 Lean 服务器的 docker 镜像。这两个部分可以使用 `npm run build:client` 和 `npm run build:server` 分别构建。

* `npm run production`：以生产模式启动项目。这需要先运行构建脚本。它将在 `PORT` 环境变量指定的端口上启动服务器，或默认在 `8080` 上启动。您可以通过运行 `PORT=80 npm run production` 在特定端口上运行。服务器将通过 http 提供 `client/dist` 中的文件，并通过 web socket 协议提供对 bubblewrapped Lean 服务器的访问。

### 环境变量

客户端和服务器端口以及默认语言可以使用环境变量配置：

* `PORT`：设置后端服务器的端口（默认：`8080`）。
* `CLIENT_PORT`：设置客户端服务器的端口（默认：`3000`）。
* `VITE_CLIENT_DEFAULT_LANGUAGE`：设置应用程序的默认语言（默认：`en`）。

确保在您的环境中适当设置这些环境变量，以根据需要配置项目。
