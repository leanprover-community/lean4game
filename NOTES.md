
# Install docker
```
sudo apt-get update
sudo apt-get install ca-certificates curl gnupg lsb-release -y
sudo mkdir -p /etc/apt/keyrings
curl -fsSL https://download.docker.com/linux/ubuntu/gpg | sudo gpg --dearmor -o /etc/apt/keyrings/docker.gpg
echo \
  "deb [arch=$(dpkg --print-architecture) signed-by=/etc/apt/keyrings/docker.gpg] https://download.docker.com/linux/ubuntu \
  $(lsb_release -cs) stable" | sudo tee /etc/apt/sources.list.d/docker.list > /dev/null
sudo apt-get update
sudo apt-get install docker-ce docker-ce-cli containerd.io docker-compose-plugin -y

sudo groupadd docker
sudo usermod -aG docker ${USER}
newgrp docker
```

# Install gVisor
```
sudo apt-get update && \
sudo apt-get install -y \
    apt-transport-https \
    ca-certificates \
    curl \
    gnupg
curl -fsSL https://gvisor.dev/archive.key | sudo gpg --dearmor -o /usr/share/keyrings/gvisor-archive-keyring.gpg
echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/gvisor-archive-keyring.gpg] https://storage.googleapis.com/gvisor/releases release main" | sudo tee /etc/apt/sources.list.d/gvisor.list > /dev/null
sudo apt-get update && sudo apt-get install -y runsc

sudo runsc install
sudo systemctl reload docker
```

# Install NPM
```
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.2/install.sh | bash
source ~/.bashrc
nvm install node npm

sudo npm install -g http-server
```

# Clone NNG interface
```
(
  git clone https://github.com/hhu-adam/nng4-interface.git
  cd nng4-interface
  rm package-lock.json
  npm install
  npm run build
)
```

```
git clone https://github.com/hhu-adam/NNG4.git
cd NNG4
docker rmi nng4:latest
docker build --pull --rm -f "Dockerfile" -t nng4:latest "."
```


# Start HTTP server
```
http-server ./nng4-interface/build
```

# Start WebSocket server
```
cd NNG4 && python3 ./gameserver.py
```

# Test docker
```
docker run --runtime=runsc --network=none --rm -it nng4:latest
```

# Running on port 80

## Set environment variable
```
export PORT=80
```
## Enable running on port 80:
```
sudo apt-get install libcap2-bin
sudo setcap cap_net_bind_service=+ep `readlink -f \`which node\``
```



# Install PM2

```
sudo npm i -g pm2

pm2 start ecosystem.config.js
pm2 save
pm2 startup
```
