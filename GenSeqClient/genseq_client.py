import json
import socket

class Client:
    def __init__(self, ip, port):
        self.ip = ip
        self.port = port
        self.conn = socket.create_connection((ip, port))
        self.sock = self.conn.makefile("rw")

    def send(self, obj):
        data = json.dumps(obj)
        self.sock.write(data + "\n")
        self.sock.flush()

    def receive(self):
        data = self.sock.readline()
        if not data:
            raise ValueError("server returned empty string (might have crashed)")
        return json.loads(data)

    def req(self, obj):
        self.send(obj)
        return self.receive()

    def is_ready(self):
        return self.req({'cmd': 'ready'})
    