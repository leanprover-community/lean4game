
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
pm2 install pm2-logrotate

```


# Nginx installieren
```
sudo apt update
sudo apt upgrade
sudo apt install nginx nginx-extras
```

Konfigurieren als reverse proxy:
```
sudo unlink /etc/nginx/sites-enabled/default
cd /etc/nginx/sites-available
sudo vim reverse-proxy.conf
```

```
# Anonymize IP addresses
map $remote_addr $remote_addr_anon {
    ~(?P<ip>\d+\.\d+\.\d+)\.    $ip.0;
    ~(?P<ip>[^:]+:[^:]+):       $ip::;
    127.0.0.1                   $remote_addr;
    ::1                         $remote_addr;
    default                     0.0.0.0;
}

log_format  main  '$remote_addr_anon - $remote_user [$time_local] "$request" '
    '$status $body_bytes_sent "$http_referer" '
    '"$http_user_agent" "$http_x_forwarded_for"';

server {
        server_name lean.math.uni-duesseldorf.de;
        location / {
                proxy_pass      http://localhost:8001;
                proxy_set_header Host $host;
                proxy_set_header X-Real-IP $remote_addr;
                proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
                proxy_http_version 1.1;
                proxy_set_header Upgrade $http_upgrade;
                proxy_set_header Connection "upgrade";

        }
        client_max_body_size 0;

        listen 443 ssl;
        ssl_certificate /home/adam/adam_math_uni-duesseldorf_de_cert.cer;
        ssl_certificate_key /home/adam/private_ssl_key.pem;

        access_log /var/log/nginx/access.log main;
        error_log /dev/null crit;
}

server {
        server_name adam.math.uni-duesseldorf.de;
        location / {
                proxy_pass      http://localhost:8002;
                proxy_set_header Host $host;
                proxy_set_header X-Real-IP $remote_addr;
                proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
                proxy_http_version 1.1;
                proxy_set_header Upgrade $http_upgrade;
                proxy_set_header Connection "upgrade";

        }
        client_max_body_size 0;

        listen 443 ssl;
        ssl_certificate /home/adam/adam_math_uni-duesseldorf_de_cert.cer;
        ssl_certificate_key /home/adam/private_ssl_key.pem;

        access_log /var/log/nginx/access.log main;
        error_log /dev/null crit;
}

# Redirect HTTP to HTTPS
server {
    listen 80 default_server;
    server_name _;
    return 301 https://$host$request_uri;
}
```

Activate config:
```
  sudo ln -s /etc/nginx/sites-available/reverse-proxy.conf /etc/nginx/sites-enabled/reverse-proxy.conf
  sudo nginx -t
  sudo nginx -s reload
```
