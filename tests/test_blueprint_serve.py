import os
import unittest
from unittest.mock import MagicMock, patch
from invoke import Context
from blueprint import tasks


class ServeTests(unittest.TestCase):
    def test_server_lifecycle(self):
        for random_port in (False, True):
            for error in (KeyboardInterrupt, RuntimeError):
                with self.subTest(random_port=random_port, error=error):
                    server = MagicMock()
                    server.__enter__.return_value = server
                    server.server_address = ("0.0.0.0", 8123)
                    server.serve_forever.side_effect = error
                    cwd = os.getcwd()
                    with patch.object(tasks.socketserver, "TCPServer", return_value=server) as factory:
                        if error is RuntimeError:
                            with self.assertRaises(RuntimeError):
                                tasks.serve.body(Context(), random_port=random_port)
                        else:
                            tasks.serve.body(Context(), random_port=random_port)
                    self.assertEqual(os.getcwd(), cwd)
                    self.assertEqual(factory.call_args.args[0], ("", 0 if random_port else 8000))
                    self.assertEqual(factory.call_args.args[1].keywords["directory"],
                                     str(tasks.BP_DIR / "web"))
                    server.__exit__.assert_called_once()
