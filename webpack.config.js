const path = require("path");
const webpack = require('webpack');
const ReactRefreshWebpackPlugin = require('@pmmmwh/react-refresh-webpack-plugin');
const WebpackShellPluginNext = require('webpack-shell-plugin-next');

module.exports = env => {
  const environment = process.env.NODE_ENV
  const isDevelopment = environment === 'development'

  const babelOptions = {
      presets: ['@babel/preset-env', '@babel/preset-react', '@babel/preset-typescript'],
    plugins: [
      isDevelopment && require.resolve('react-refresh/babel'),
    ].filter(Boolean),
  };

  global.$RefreshReg$ = () => {};
  global.$RefreshSig$ = () => () => {};

  return {
    entry: ["./client/src/index.tsx"],
    mode: isDevelopment ? 'development' : 'production',
    module: {
      rules: [
        {
          test: /\.(js|jsx)$/,
          exclude: [/server/, /node_modules/],
          use: [{
            loader: require.resolve('babel-loader'),
            options: babelOptions,
          }]
        },
        {
          test: /\.tsx?$/,
          use: [{
            loader: 'ts-loader',
            options: { allowTsInNodeModules: true }
          }],
          exclude: /node_modules(?!\/(lean4web|lean4|lean4-infoview))/,
          // Allow .ts imports from node_modules/lean4web and node_modules/lean4
        },
        {
          test: /\.css$/,
          use: ["style-loader", "css-loader"]
        },
        {
          test: /\.(jpg|png)$/,
          use: {
            loader: 'file-loader',
          },
        },
      ]
    },
    resolve: {
      extensions: ["*", ".js", ".jsx", ".tsx", ".ts"],
      fallback: {
        "http": require.resolve("stream-http") ,
        "path": require.resolve("path-browserify")
      },
    },
    output: {
      path: path.resolve(__dirname, "client/dist/"),
      filename: "bundle.js",
    },
    devServer: {
      proxy: {
        '/websocket': {
           target: 'ws://localhost:8080',
           ws: true
        },
        '/import': {
          target: 'http://localhost:3000',
          router: () => 'http://localhost:8080',
        },
      },
      static: path.join(__dirname, 'client/public/'),
      port: 3000,
      hot: true,
    },
    devtool: "source-map",
    plugins: [
      !isDevelopment && new WebpackShellPluginNext({
        onBuildEnd:{
          scripts: [
            // It's hard to set up webpack to copy the index.html correctly,
            // so we copy it explicitly after every build:
            'cp client/public/index.html client/dist/',
            // Similarly, I haven't been able to load `onigasm.wasm` properly:
            'cp client/public/onigasm.wasm client/dist/',],
          blocking: false,
          parallel: true
        }
      }),
      isDevelopment && new ReactRefreshWebpackPlugin(),
    ].filter(Boolean),

    // Webpack is not happy about the dynamically loaded widget code in the function
    // `dynamicallyLoadComponent` in `infoview/userWidget.tsx`. If we want to support
    // dynamically loaded widget code, we need to make sure that the files are available.
    ignoreWarnings: [/Critical dependency: the request of a dependency is an expression/]
  };
}
