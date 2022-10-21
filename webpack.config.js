const path = require("path");
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
          use: 'ts-loader',
          exclude: /node_modules/,
        },
        {
          test: /\.css$/,
          use: ["style-loader", "css-loader"]
        }
      ]
    },
    resolve: { extensions: ["*", ".js", ".jsx", ".tsx", ".ts"] },
    output: {
      path: path.resolve(__dirname, "client/dist/"),
      filename: "bundle.js",
      sourceMapFilename: "[name].js.map"
    },
    devServer: {
      proxy: {
        '/websocket': {
           target: 'ws://localhost:8080',
           ws: true
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
          // It's hard to set up webpack to copy the index.html correctly,
          // so we copy it explicitly after every build:
          scripts: ['cp client/public/index.html client/dist/'],
          blocking: false,
          parallel: true
        }
      }),
      isDevelopment && new ReactRefreshWebpackPlugin()
    ].filter(Boolean),
  };
}
