## yet another parser generator

currently, we only support LR(0) and partially support SLR

we have a long term plan for inplementing LALR algorithm, which is the most commonly used parsing algirithm in parser generators.

however, it's a little bit complicated since each term is related with a lookahead set.

feel free to implement it by yourself, PR is welcomed.