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
    "name": "foo",
    "offset": 1,
    "source": "x + 2"
}
```

### Response format

The response is a JSON string with the format:
```json
{"status": true, "lean": "def foo (n : ℕ) : ℤ :=\n  let x := n - 1\n  (x + 2)", "error": null}
```
or, in case of error:
```json
{"status": false, "error": "error message"}
```

## Authors

* Walter Moreira
* Joe Stubbs

## License

MIT
