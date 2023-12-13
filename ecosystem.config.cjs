// This is a configuration file for pm2, a production process manager for nodejs
module.exports = {
  apps : [{
    name   : "lean4game",
    script : "relay/index.mjs",
    env: {
      LEAN4GAME_GITHUB_USER: "",
      LEAN4GAME_GITHUB_TOKEN: "",
      NODE_ENV: "production",
      PORT: 8002
    },
  }]
}
