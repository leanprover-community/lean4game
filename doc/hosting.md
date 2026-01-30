# Example for hosting Lean4Game yourself

These instructions aim to give you an exemplary manual on how to host your
Theseelean4game instance, such that, others can access it via the internet.
This manual will assume that you already have a running Linux server that
uses the `apt` package manager.
(the steps are analogous for other Linux distributions and their package managers).

## Download Dependencies

In this section we will use nginx for our server, but any other web server might be applied here.
Analogously, the same logic applies to pm2 as our choice for process management tool.

1. Install a ```nginx``` web server as reverse proxy

 ```shell
    sudo apt update
    sudo apt install nginx
 ```

2. install ```npm``` for building JavaScript projects

 ```shell
   curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.2/install.sh | bash
   source ~/.bashrc
   nvm install node npm
```

3. install ```pm2``` to manage processes on the server

 ```shell
    sudo npm install pm2 -g
 ```

4. install ```tsc``` to compile TypeScript projects on the server

 ```shell
    sudo npm install typescript -g
 ```

5. Install ```bubblewrap``` for secure execution of lean server

 ```shell
   sudo apt-get install bubblewrap
 ```

5. install ```elan``` to manage versions of the Lean4 programming language and theorem prover

 ```shell
    curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
 ```

 This will install the current version of elan with a default installation of lean and the lake package manager.

6. Conclude ```elan``` installation by configuring your current shell to it

 ```shell
    source $HOME/.elan/env
 ```
## Setup Reverse Proxy

The next step would include setting up a reverse proxy with nginx and adding
information concerning domain and SSL certification. As those considerations are
quite individual, technical and safety critical, we will refer here to a general instruction on how
to set up a reverse [proxy using nginx on Ubuntu](https://www.digitalocean.com/community/tutorials/how-to-configure-nginx-as-a-reverse-proxy-on-ubuntu-22-04).

## Setting up Lean4Game

This section will be somewhat similar to what is written in the section about
[running Lean4Game locally](running_locally.md).
We diverge here in the sense, that we are only describing the installation of Lean4Game itself.
Before starting, you will need to generate a [GitHub access token](https://docs.github.com/en/authentication/keeping-your-account-and-data-secure/managing-your-personal-access-tokens).

1. Clone hosted projects via ```git``` onto server. **Important:** Please use the HTTPS URL from GitHub, not the SSH URL, to clone the project repositories.

 ```shell
    git clone https://github.com/leanprover-community/lean4game.git
 ```

2. Install lean4game dependencies via ```npm```

 ```shell
    cd lean4game
    npm install
 ```

3. Set lean4game environment variables in ```ecosystem.config.cjs``` file

To get the GitHub Access Token required for fields ```LEAN4GAME_GITHUB_USER``` and ```LEAN4GAME_GITHUB_TOKEN``` please refer to the dedicated [instructions](./Updating/updating_github_access_token.md).

```vim
// This is a configuration file for pm2, a production process manager for nodejs
module.exports = {
  apps : [{
    name   : "lean4game",
    script : "relay/dist/src/index.js",
    env: {
      LEAN4GAME_GITHUB_USER: "<to-be-requested-from-admin>",
      LEAN4GAME_GITHUB_TOKEN: "<to-be-requested-from-admin>",
      RESERVED_DISC_SPACE_MB: <RESERVED_SPACE>,
      ISSUE_CONTACT: "<contact_link>",
      NODE_ENV: "production",
      PORT: <PORT>,
      API_PORT: <API_PORT>,
    },
  }]
}
```

4. Build lean4game project via ```npm```

 ```shell
    npm run build
 ```

5. Start Lean4Game through PM2

```shell
   pm2 start ecosystem.config.cjs
```

Having done that you should be able to now access your hosted Lean4Game instance via the domain that has been specified during the setup of the nginx server. For more information on how to maintain your established server please refer to the [server maintenance documentation](server.md)
