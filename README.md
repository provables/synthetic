# GenSeq Server

A "Lean Server" for transpiling and evaluating OEIS sequences.

## Using

The easiest way to run this server is using [Nix](https://nixos.org).

Clone the repository and run `nix develop` in the directory.

Once in the environment, run `task -a` to list all the tasks available. In particular, 
`task supervise` will start the Lean server under the control of a supervisor (so if it crashes
it will be restarted automatically). Alternatively, you can use `lake exe genseq` for running
the server manually.

Access the server at `localhost:8000`. For example:

```bash
⌘ ➜ echo '{"cmd": "ready"}' | nc localhost 8000 | jq
{
  "status": true,
  "result": {
    "status": "ready"
  },
  "error": null
}
```

Stop the supervisor with `task stop-supervise`.

## Extending

You can add new commands to the server by writing a function with signature:

```lean
Json -> GenSeqExcept Json
```

in the file `GenSeq/Main.lean`, and adding the corresponding entry to the hashmap `Commands`.

The function will receive the the arguments of the command. For example, if the server receives
the command:

```json
{
    "cmd": "eval",
    "args": {
        "src": "...",
        "values": [...]
    }
}
```

then the function will receive the JSON object `{"src": "...", "values": [...]}`. The return object
from the function will be the JSON object under the `"result"` key.
