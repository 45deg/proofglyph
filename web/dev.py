#!/usr/bin/env python3
"""Build the browser demo on changes and reload connected browsers."""

import argparse
import functools
import json
from pathlib import Path
import subprocess
import threading
import time
from http.server import SimpleHTTPRequestHandler, ThreadingHTTPServer


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "_build/default/web"
WATCH = (ROOT / "web", ROOT / "lib", ROOT / "examples", ROOT / "dune-project")
RELOAD = """<script>
(() => {
  let version;
  async function poll() {
    try {
      const response = await fetch('/__dev_version', {cache: 'no-store'});
      if (!response.ok) return;
      const next = await response.json();
      if (version !== undefined && version !== next) location.reload();
      version = next;
    } catch (_) {}
  }
  poll();
  setInterval(poll, 700);
})();
</script>"""


def snapshot():
    result = {}
    for entry in WATCH:
        paths = entry.rglob("*") if entry.is_dir() else (entry,)
        for path in paths:
            if "__pycache__" in path.parts or path.name.startswith("."):
                continue
            try:
                if path.is_file():
                    stat = path.stat()
                    result[str(path)] = (stat.st_mtime_ns, stat.st_size)
            except FileNotFoundError:
                pass
    return result


def build():
    print("Building @web/browser…", flush=True)
    return subprocess.run(["dune", "build", "@web/browser"], cwd=ROOT).returncode == 0


class Handler(SimpleHTTPRequestHandler):
    version = str(time.time_ns())

    def end_headers(self):
        self.send_header("Cache-Control", "no-store")
        super().end_headers()

    def do_GET(self):
        path = self.path.split("?", 1)[0]
        if path == "/__dev_version":
            self.send_bytes(json.dumps(Handler.version).encode(), "application/json")
        elif path in ("/", "/index.html"):
            try:
                html = (OUTPUT / "index.html").read_text()
            except FileNotFoundError:
                self.send_error(503, "Waiting for a successful build")
                return
            self.send_bytes(html.replace("</body>", RELOAD + "</body>").encode(),
                            "text/html; charset=utf-8")
        else:
            super().do_GET()

    def send_bytes(self, content, content_type):
        self.send_response(200)
        self.send_header("Content-Type", content_type)
        self.send_header("Content-Length", str(len(content)))
        self.end_headers()
        self.wfile.write(content)

    def log_message(self, format, *args):
        if self.path.split("?", 1)[0] != "/__dev_version":
            super().log_message(format, *args)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--port", type=int, default=8765)
    args = parser.parse_args()
    handler = functools.partial(Handler, directory=str(OUTPUT))
    try:
        server = ThreadingHTTPServer(("127.0.0.1", args.port), handler)
    except OSError as error:
        parser.exit(1, f"Cannot start server: {error}. Try --port 8767.\n")
    try:
        previous = snapshot()
        build()
        threading.Thread(target=server.serve_forever, daemon=True).start()
        print(f"http://127.0.0.1:{args.port} — watching web/, lib/, examples/ (Ctrl+C to stop)",
              flush=True)
        while True:
            time.sleep(0.4)
            current = snapshot()
            if current == previous:
                continue
            # Wait until a burst of saves has settled before starting Dune.
            while True:
                time.sleep(0.2)
                settled = snapshot()
                if settled == current:
                    break
                current = settled
            previous = current
            if build():
                Handler.version = str(time.time_ns())
                print("Build succeeded; reloading browsers.", flush=True)
            else:
                print("Build failed; waiting for the next edit.", flush=True)
    except KeyboardInterrupt:
        print("\nStopped.", flush=True)
    finally:
        server.server_close()


if __name__ == "__main__":
    main()
