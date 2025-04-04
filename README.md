docker build -t trading-bot .
docker run --rm --env-file .env trading-bot
