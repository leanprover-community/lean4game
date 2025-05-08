// This is a configuration file for pm2, a production process manager for nodejs
module.exports = {
  apps : [{
    name   : "lean4game",
    script : "relay/dist/index.js",
    env: {
      LEAN4GAME_GITHUB_USER: "",
      LEAN4GAME_GITHUB_TOKEN: "",
      RESERVED_DISC_SPACE_MB: 0,
      ISSUE_CONTACT: "",
      NODE_ENV: "production",
      PORT: 8002
    },
  }]
}
