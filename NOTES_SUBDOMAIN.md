## Certificate for multiple subdomains:

Make a copy of the `openssl.cnf` file:
```
cp /etc/ssl/openssl.cnf ~/
```

Edit the file:
```
vim ~/openssl.cnf
```

Uncomment following line in the `[req]` section:
```
req_extensions = v3_req 
```

In the `[v3_req]` section, add the following line:
```
subjectAltName = @alt_names
```

Create a new section `[ alt_names ]` at the bottom of the config file. Add SAN or DNS or Alt names like this.

```
[ alt_names ]
DNS.1 = lean.math.uni-duesseldorf.de
```

Note: Do not add the domain name used in the common name field again.

Save and quit.

Create a private key
```
sudo openssl genpkey -algorithm RSA -pkeyopt rsa_keygen_bits:4096 -out /etc/ssl/private/private.pem
```

Generate the CSR:
```
 sudo openssl req -new -key /etc/ssl/private/private.pem -out ~/public.csr -config ~/openssl.cnf 
```

```
Country Name (2 letter code) [AU]:DE
State or Province Name (full name) [Some-State]:Nordrhein-Westfalen
Locality Name (eg, city) []:Duesseldorf
Organization Name (eg, company) [Internet Widgits Pty Ltd]:Heinrich-Heine-Universitaet Duesseldorf
Organizational Unit Name (eg, section) []:ZIM
Common Name (e.g. server FQDN or YOUR name) []:adam.math.uni-duesseldorf.de // Die Domain, die oben ausgelassen wurde
Email Address []:alexander.bentkamp@hhu.de //(Ihre Mailadresse)
 
A challenge password []: // leer lassen
An optional company name []: leer lassen
```

Check that the certificate contains the Common Name and all Subject Alternative Names:
```
openssl req -in public.csr -noout -text
```

Then follow the instructions here: https://wiki.hhu.de/display/HHU/Serverzertifikat+beantragen