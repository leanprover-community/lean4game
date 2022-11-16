// This is a configuration file for pm2, a production process manager for nodejs
module.exports = {
  apps : [{
    name   : "lean4game",
    script : "server/index.js",
    env: {
       NODE_ENV: "production",
    },
  }]
}
