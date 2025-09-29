FROM alpine:3.22

RUN apk update && apk add --no-cache nodejs npm

RUN npm install -g @vscode/vsce

WORKDIR /jackdawvscode
COPY . .
RUN vsce package --allow-missing-repository
