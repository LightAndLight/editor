#! /usr/bin/env sh

echo $1

case $1 in
	"webui")
		cd webui
		ghcid -c "ghci" -T "main" ;;
	"core")
		cd core
		ghcid -c "cabal new-repl" ;;
	"editor")
		cd editor
		ghcid -c "cabal new-repl" ;;
esac
