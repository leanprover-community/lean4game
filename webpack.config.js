const path = require("path");
const webpack = require("webpack");
const ReactRefreshWebpackPlugin = require('@pmmmwh/react-refresh-webpack-plugin');

module.exports = env => {
  const isDevelopment = env.NODE_ENV !== 'production';
  
  const babelOptions = {
    presets: ['@babel/preset-env', '@babel/preset-react'],
    plugins: [
      isDevelopment && require.resolve('react-refresh/babel'),
    ].filter(Boolean),
  };

  global.$RefreshReg$ = () => {};
  global.$RefreshSig$ = () => () => {};

  return {
    entry: "./client/src/index.js",
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
          test: /\.css$/,
          use: ["style-loader", "css-loader"]
        },
        {
          test: /\.(woff(2)?|ttf|eot|svg)(\?v=\d+\.\d+\.\d+)?$/,
          use: [
          {
            loader: 'file-loader',
            options: {
              name: '[name].[ext]',
              outputPath: 'fonts/'
            }
          }
          ]
        }
      ]
    },
    resolve: { extensions: ["*", ".js", ".jsx"] },
    output: {
      path: path.resolve(__dirname, "client/dist/"),
      publicPath: "/client/dist/",
      filename: "bundle.js"
    },
    devServer: {
      contentBase: path.join(__dirname, "client/public/"),
      port: 3000,
      publicPath: "http://localhost:3000/dist/",
      hotOnly: true
    },
    plugins: [isDevelopment && new ReactRefreshWebpackPlugin()].filter(Boolean),
  };
}