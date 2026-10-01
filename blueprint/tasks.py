import os
from functools import partial
from pathlib import Path
import http.server
import socketserver

from invoke import run, task

BP_DIR = Path(__file__).parent

@task
def print_bp(ctx):
    cwd = os.getcwd()
    os.chdir(BP_DIR)
    run('mkdir -p print && cd src && xelatex -output-directory=../print print.tex')
    os.chdir(cwd)

@task
def bp(ctx):
    cwd = os.getcwd()
    os.chdir(BP_DIR)
    run('mkdir -p print && cd src && xelatex -output-directory=../print print.tex')
    run('cd src && xelatex -output-directory=../print print.tex')
    os.chdir(cwd)

@task
def bptt(ctx):
    """
    Build the blueprint PDF file with tectonic and prepare src/web.bbl for task `web`

    NOTE: install tectonic by running `curl --proto '=https' --tlsv1.2 -fsSL https://drop-sh.fullyjustified.net |sh` in
    `~/.local/bin/`
    """

    cwd = os.getcwd()
    os.chdir(BP_DIR)
    run('mkdir -p print && cd src && tectonic -Z shell-escape-cwd=. --keep-intermediates --outdir ../print print.tex')
    # run('cp print/print.bbl src/web.bbl')
    os.chdir(cwd)

@task
def web(ctx):
    cwd = os.getcwd()
    os.chdir(BP_DIR/'src')
    run('plastex -c plastex.cfg web.tex')
    os.chdir(cwd)

@task
def serve(ctx, random_port=False):
    Handler = partial(http.server.SimpleHTTPRequestHandler, directory=str(BP_DIR/'web'))
    # Let the OS choose an available port rather than guessing an unused one.
    port = 0 if random_port else 8000
    with socketserver.TCPServer(("", port), Handler) as httpd:
        (_, port) = httpd.server_address
        print(f'Serving http://localhost:{port}/ ...')
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            pass
