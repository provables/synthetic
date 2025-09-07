# Gen Seq

Run a server that converts the synthetic DSL to a Lean definition.

## Usage

Start a development environment with `nix develop`.

Run `task -a` to see all the tasks available. The common ones are:

* `task run`: build, compile into an executable, and run the server on default port 8000.
* `task run -- -p 1234`: same as before but on port 1234.
* `task run -- -h`: display help.

### Request format

Write a JSON string terminated with `\n`, with the following format:
```json
{
    "cmd": "gen",
    "args": {
        "name": "foo",
        "offset": 1,
        "source": "x + 2"
    }
}
```
Other commands will be added in the future.

### Response format

The response is a JSON string with the format:
```json
{
    "status": true, 
    "result" : {
        "lean": "def foo (n : ℕ) : ℤ :=\n  let x := n - 1\n  (x + 2)"
    }
}
```
or, in case of error:
```json
{
    "status": false, 
    "error": "error message"
}
```

## Extending the server

For adding a new command to the server, write a function with signature:
```lean
Json → GenSeqExcept Json
```
The monad `GenSeqExcept` gives access to `IO`, `Except`, and the context `GenSeqContext` that
contains the environment with the imported module. The input is the JSON object `args`, and the
output would be sent back as `result`.

Update the HashMap `Commands` to associate a name for the command to the function.

Those two changes should be enough for the server to respond to the new command.

## Authors

* Walter Moreira
* Joe Stubbs

## License

MIT
