from lark import Lark

with open("basic.ebnf", "r") as f:
    basic = f.read()
parser_basic = Lark(basic, start='expr')
texts = ["1 + x", "2- y", "1* 2", "x mod y", "2 div 1"]
[parser_basic.parse(text) for text in texts]


with open("full.ebnf", "r") as f:
    full = f.read()
parser_full = Lark(full, start='expr')
texts = ["(2)", "(x)", "(1 + x)", "(2- y)","(x + (1 + y))", "((x + y) * (1 + y))", "(1 * (2 div y))"]
[parser_full.parse(text) for text in texts]

