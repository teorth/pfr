import os
import random
from contextlib import contextmanager
from pathlib import Path
import http.server
import socketserver

from invoke import run, task

BP_DIR = Path(__file__).parent

@contextmanager
def blueprint_directory(path):
    """Restore the caller's directory even if a build command fails."""
    cwd = os.getcwd()
    try:
        os.chdir(path)
        yield
    finally:
        os.chdir(cwd)

@task
def print_bp(ctx):
    with blueprint_directory(BP_DIR):
        run('mkdir -p print && cd src && xelatex -output-directory=../print print.tex')

@task
def bp(ctx):
    with blueprint_directory(BP_DIR):
        run('mkdir -p print && cd src && xelatex -output-directory=../print print.tex')
        run('cd src && xelatex -output-directory=../print print.tex')

@task
def bptt(ctx):
    """
    Build the blueprint PDF file with tectonic and prepare src/web.bbl for task `web`

    NOTE: install tectonic by running `curl --proto '=https' --tlsv1.2 -fsSL https://drop-sh.fullyjustified.net |sh` in
    `~/.local/bin/`
    """

    with blueprint_directory(BP_DIR):
        run('mkdir -p print && cd src && tectonic -Z shell-escape-cwd=. --keep-intermediates --outdir ../print print.tex')
        # run('cp print/print.bbl src/web.bbl')

@task
def web(ctx):
    with blueprint_directory(BP_DIR/'src'):
        run('plastex -c plastex.cfg web.tex')

@task
def serve(ctx, random_port=False):
    cwd = os.getcwd()
    os.chdir(BP_DIR/'web')
    Handler = http.server.SimpleHTTPRequestHandler
    if random_port:
        port = random.randint(8000, 8100)
    else:
        port = 8000

    httpd = socketserver.TCPServer(("", port), Handler)
    try:
        (ip, port) = httpd.server_address
        ip = ip or 'localhost'
        print(f'Serving http://{ip}:{port}/ ...')
        httpd.serve_forever()
    except KeyboardInterrupt:
        pass
    httpd.server_close()
