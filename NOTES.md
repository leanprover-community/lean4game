
# Install Lean
wget -q https://raw.githubusercontent.com/leanprover-community/mathlib4/master/scripts/install_debian.sh && bash install_debian.sh ; rm -f install_debian.sh && source ~/.profile

# Install NPM
```
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.2/install.sh | bash
source ~/.bashrc
nvm install node npm

npm install -g http-server
```

# Clone NNG interface

```
git clone https://github.com/hhu-adam/NNG4.git
cd NNG4
docker rmi nng4:latest
docker build --pull --rm -f "Dockerfile" -t nng4:latest "."
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
        server_name lean.math.hhu.de;
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

        access_log /var/log/nginx/access.log main;
        error_log /dev/null crit;

        listen 443 ssl;
        ssl_certificate /home/adam/adam_math_hhu_de_cert.cer;
        ssl_certificate_key /etc/ssl/private/private.pem;
}

server {
        server_name adam.math.hhu.de;
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
        ssl_certificate /home/adam/adam_math_hhu_de_cert.cer;
        ssl_certificate_key /etc/ssl/private/private.pem;

        access_log /var/log/nginx/access.log main;
        error_log /dev/null crit;
}

server {
        server_name adam-dev.math.hhu.de;
        location / {
                proxy_pass      http://localhost:8003;
                proxy_set_header Host $host;
                proxy_set_header X-Real-IP $remote_addr;
                proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
                proxy_http_version 1.1;
                proxy_set_header Upgrade $http_upgrade;
                proxy_set_header Connection "upgrade";

        }
        client_max_body_size 0;

        listen 443 ssl;
        ssl_certificate /home/adam/adam_math_hhu_de_cert.cer;
        ssl_certificate_key /etc/ssl/private/private.pem;

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


## Install `unzip` for Importing Docker Images

```
sudo apt-get install unzip
```

## Install bubblewrap (bwrap)
```
sudo apt-get install bubblewrap
```
