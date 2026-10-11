function countdownSum(n: nat): nat
    decreases n
{
    if n <= 2 then 0
    else n + countdownSum(n - 2)
}

function sumSeq(s: seq<int>): int
    decreases |s|
{
    if |s| == 0 then 0
    else s[|s| - 1] + sumSeq(s[..|s|-1])
}

function weird(m: nat, n: nat): nat
    decreases m,n
{
    if m == 0 then n
    else if n == 0 then weird(m - 1, 1)
    else weird(m - 1, weird(m, n - 1))
}

function even(n: nat): bool
    decreases n
{
    if n == 0 then true
    else odd(n - 1)
}

function odd(n: nat): bool
    decreases n
{
    if n == 0 then false
    else even(n - 1)
}