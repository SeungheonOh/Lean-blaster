#!/usr/bin/env python3
"""Differential fuzzer for Blaster: random Lean propositions, blaster verdict vs Lean evaluation.

Usage: python3 -I gen.py <outdir> <seed> <nprops> <mode> [perfile] [profile]
  mode = ground | quant
Writes <outdir>/blast_<i>.lean, <outdir>/oracle_<i>.lean, <outdir>/props.jsonl
"""
import json, os, random, sys

PRE = r"""
structure Pt where
  x : Nat
  y : Int
deriving DecidableEq, Repr

inductive Color where
  | red | green | blue
deriving DecidableEq, Repr

inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree
deriving DecidableEq, Repr

def Tree.size : Tree → Nat
  | .leaf => 0
  | .node l _ r => l.size + 1 + r.size

def Color.next : Color → Color
  | .red => .green
  | .green => .blue
  | .blue => .red

def fz1 (n : Nat) : Nat :=
  match n with
  | 0 => 1
  | 1 => 5
  | n+2 => n

def fz2 (a : Int) (b : Nat) : Int :=
  if a < 0 then a + b else a - b

def fzb (n : Nat) (b : Bool) : Bool :=
  match n, b with
  | 0, _ => b
  | _, true => false
  | _, false => true

def fzsum : List Nat → Nat
  | [] => 0
  | x :: xs => x + fzsum xs

def fzcount (k : Nat) : List Nat → Nat
  | [] => 0
  | x :: xs => if x = k then fzcount k xs + 1 else fzcount k xs

def natVals : List Nat := [0, 1, 2, 3, 4, 5, 7, 8, 10, 16, 255, 256]
def natValsS : List Nat := [0, 1, 2, 3, 5, 10]
def intVals : List Int := [-100, -8, -7, -3, -2, -1, 0, 1, 2, 3, 7, 8, 100]
def intValsS : List Int := [-7, -2, -1, 0, 1, 2, 5]
def boolVals : List Bool := [false, true]
def strVals : List String := ["", "a", "b", "ab", "ba", "aa", "abc", "hello", "a\"b", "é"]
def lstVals : List (List Nat) := [[], [0], [1], [3], [1, 2], [2, 1], [0, 0], [1, 2, 3], [5, 3, 1, 4]]
def optVals : List (Option Nat) := [none, some 0, some 1, some 5]
def charVals : List Char := ['a', 'b', '0', 'Z', ' ']
"""

NAT_LITS = [0, 0, 1, 1, 2, 3, 4, 5, 7, 8, 10, 16, 100, 255, 256]
INT_LITS = [0, 1, -1, 2, -2, 3, -3, 4, -4, 5, -7, 7, -8, 8, 100, -100]
STR_LITS = ['""', '"a"', '"b"', '"ab"', '"ba"', '"abc"', '"hello"', '"aa"']
CHR_LITS = ["'a'", "'b'", "'0'", "'Z'", "' '"]
LST_LITS = ["([] : List Nat)", "[(0:Nat)]", "[(1:Nat)]", "[(1:Nat), 2]", "[(2:Nat), 1]",
            "[(1:Nat), 2, 3]", "[(0:Nat), 0]", "[(5:Nat), 3, 1, 4]"]

VAL_LISTS = {"Nat": "natVals", "Int": "intVals", "Bool": "boolVals", "String": "strVals",
             "List Nat": "lstVals", "Option Nat": "optVals", "Char": "charVals"}
VAL_LISTS_S = dict(VAL_LISTS, Nat="natValsS", Int="intValsS")


class G:
    def __init__(self, rng, profile):
        self.r = rng
        self.prof = profile
        self.ctr = 0
        self.pool = {}

    def fresh(self, p="k"):
        self.ctr += 1
        return f"{p}{self.ctr}"

    def ch(self, xs):
        return self.r.choice(xs)

    def coin(self, p):
        return self.r.random() < p

    def var(self, env, ty):
        vs = env.get(ty, [])
        return self.ch(vs) if vs else None

    def remember(self, ty, t):
        self.pool.setdefault(ty, []).append(t)
        return t

    def gen(self, ty, d, env):
        # shared sub-term reuse
        if ty in self.pool and self.pool[ty] and self.coin(0.12):
            return self.ch(self.pool[ty])
        f = getattr(self, "g_" + ty.replace(" ", "_").replace("×", "x"))
        t = f(d, env)
        if d >= 1 and self.coin(0.3):
            self.remember(ty, t)
        return t

    # ---------------- Nat ----------------
    def g_Nat(self, d, env):
        v = self.var(env, "Nat")
        if d <= 0:
            if v and self.coin(0.6):
                return v
            return f"({self.ch(NAT_LITS)} : Nat)"
        n = lambda: self.gen("Nat", d - 1, env)
        i = lambda: self.gen("Int", d - 1, env)
        opts = [
            lambda: f"({n()} + {n()})", lambda: f"({n()} - {n()})", lambda: f"({n()} * {n()})",
            lambda: f"({n()} / {n()})", lambda: f"({n()} % {n()})",
            lambda: f"({n()} ^ ({self.ch([0, 1, 2, 3])} : Nat))",
            lambda: f"(Nat.min {n()} {n()})", lambda: f"(Nat.max {n()} {n()})",
            lambda: f"(min {n()} {n()})", lambda: f"(max {n()} {n()})",
            lambda: f"(Nat.pred {n()})", lambda: f"(Nat.succ {n()})",
            lambda: f"(Nat.log2 {n()})", lambda: f"(Nat.gcd {n()} {n()})", lambda: f"(Nat.lcm {n()} {n()})",
            lambda: f"(Int.toNat {i()})", lambda: f"(Int.natAbs {i()})",
            lambda: f"(List.length {self.gen('List Nat', d-1, env)})",
            lambda: f"(String.length {self.gen('String', d-1, env)})",
            lambda: f"(Option.getD {self.gen('Option Nat', d-1, env)} {n()})",
            lambda: f"(Bool.toNat {self.gen('Bool', d-1, env)})",
            lambda: f"(Char.toNat {self.gen('Char', d-1, env)})",
            lambda: f"(List.foldl (· + ·) {n()} {self.gen('List Nat', d-1, env)})",
            lambda: f"(List.foldl (fun a b => a * 2 + b) {n()} {self.gen('List Nat', d-1, env)})",
            lambda: f"(fzsum {self.gen('List Nat', d-1, env)})",
            lambda: f"(fzcount {n()} {self.gen('List Nat', d-1, env)})",
            lambda: f"(fz1 {n()})",
            lambda: f"(Tree.size {self.gen('Tree', d-1, env)})",
            lambda: f"(Pt.x {self.gen('Pt', d-1, env)})",
            lambda: f"({self.gen('Prod', d-1, env)}).1",
            lambda: f"(String.toList {self.gen('String', d-1, env)}).length",
            lambda: self.ite("Nat", d, env), lambda: self.ite("Nat", d, env), lambda: self.dite("Nat", d, env),
            lambda: self.match_nat("Nat", d, env), lambda: self.match_nat("Nat", d, env),
            lambda: self.match_opt("Nat", d, env), lambda: self.match_list("Nat", d, env),
            lambda: self.match_bool("Nat", d, env),
        ]
        if v:
            opts += [lambda: v] * 4
        return self.ch(opts)()

    # ---------------- Int ----------------
    def g_Int(self, d, env):
        v = self.var(env, "Int")
        if d <= 0:
            if v and self.coin(0.6):
                return v
            k = self.ch(INT_LITS)
            return f"({k} : Int)"
        n = lambda: self.gen("Nat", d - 1, env)
        i = lambda: self.gen("Int", d - 1, env)
        opts = [
            lambda: f"({i()} + {i()})", lambda: f"({i()} - {i()})", lambda: f"({i()} * {i()})",
            lambda: f"({i()} / {i()})", lambda: f"({i()} % {i()})",
            lambda: f"(Int.emod {i()} {i()})", lambda: f"(Int.ediv {i()} {i()})",
            lambda: f"(Int.bmod {i()} {n()})", lambda: f"(Int.bdiv {i()} {n()})",
            lambda: f"(- {i()})", lambda: f"(Int.neg {i()})",
            lambda: f"({i()} ^ ({self.ch([0, 1, 2, 3])} : Nat))",
            lambda: f"(min {i()} {i()})", lambda: f"(max {i()} {i()})",
            lambda: f"(({n()} : Nat) : Int)", lambda: f"(Int.ofNat {n()})",
            lambda: f"(Int.negSucc {n()})", lambda: f"(Int.sign {i()})",
            lambda: f"(Int.subNatNat {n()} {n()})",
            lambda: f"(Option.getD {self.gen('Option Int', d-1, env)} {i()})",
            lambda: f"(Pt.y {self.gen('Pt', d-1, env)})",
            lambda: f"({self.gen('Prod', d-1, env)}).2",
            lambda: f"(fz2 {i()} {n()})",
            lambda: self.ite("Int", d, env), lambda: self.ite("Int", d, env), lambda: self.dite("Int", d, env),
            lambda: self.match_nat("Int", d, env), lambda: self.match_int("Int", d, env),
            lambda: self.match_bool("Int", d, env),
        ]
        if "tdiv" in self.prof:
            opts += [lambda: f"(Int.tdiv {i()} {i()})", lambda: f"(Int.fdiv {i()} {i()})",
                     lambda: f"(Int.tmod {i()} {i()})", lambda: f"(Int.fmod {i()} {i()})"]
        if v:
            opts += [lambda: v] * 4
        return self.ch(opts)()

    # ---------------- Bool ----------------
    def g_Bool(self, d, env):
        v = self.var(env, "Bool")
        if d <= 0:
            if v and self.coin(0.6):
                return v
            return self.ch(["true", "false"])
        b = lambda: self.gen("Bool", d - 1, env)
        n = lambda: self.gen("Nat", d - 1, env)
        i = lambda: self.gen("Int", d - 1, env)
        s = lambda: self.gen("String", d - 1, env)
        l = lambda: self.gen("List Nat", d - 1, env)
        opts = [
            lambda: f"({b()} && {b()})", lambda: f"({b()} || {b()})", lambda: f"(! {b()})",
            lambda: f"({b()} ^^ {b()})", lambda: f"({b()} == {b()})", lambda: f"({b()} != {b()})",
            lambda: f"({n()} == {n()})", lambda: f"({n()} != {n()})", lambda: f"({i()} == {i()})",
            lambda: f"({s()} == {s()})", lambda: f"({l()} == {l()})", lambda: f"({l()} != {l()})",
            lambda: f"(decide {self.gen('Prop', d-1, env)})", lambda: f"(decide {self.gen('Prop', d-1, env)})",
            lambda: f"(Nat.beq {n()} {n()})", lambda: f"(Nat.ble {n()} {n()})", lambda: f"(Nat.blt {n()} {n()})",
            lambda: f"(List.contains {l()} {n()})", lambda: f"(List.elem {n()} {l()})",
            lambda: f"(List.isEmpty {l()})", lambda: f"(String.isEmpty {s()})",
            lambda: f"(String.startsWith {s()} {s()})",
            lambda: f"(Option.isSome {self.gen('Option Nat', d-1, env)})",
            lambda: f"(Option.isNone {self.gen('Option Nat', d-1, env)})",
            lambda: f"(Nat.decEq {n()} {n()} |>.decide)",
            lambda: f"(fzb {n()} {b()})",
            lambda: f"(List.all {l()} (fun x => x < {n()}))",
            lambda: f"(List.any {l()} (fun x => x == {n()}))",
            lambda: self.ite("Bool", d, env), lambda: self.match_bool("Bool", d, env),
            lambda: self.match_nat("Bool", d, env),
        ]
        if v:
            opts += [lambda: v] * 3
        return self.ch(opts)()

    # ---------------- Prop ----------------
    def g_Prop(self, d, env):
        if d <= 0:
            return self.atom(0, env)
        p = lambda: self.gen("Prop", d - 1, env)
        opts = [
            lambda: f"({p()} ∧ {p()})", lambda: f"({p()} ∨ {p()})", lambda: f"({p()} → {p()})",
            lambda: f"({p()} ↔ {p()})", lambda: f"(¬ {p()})",
            lambda: self.atom(d, env), lambda: self.atom(d, env), lambda: self.atom(d, env),
            lambda: self.atom(d, env),
            lambda: self.ite("Prop", d, env),
            lambda: self.shared_impl(d, env),
        ]
        return self.ch(opts)()

    def shared_impl(self, d, env):
        # repeat an identical sub-term inside and outside an implication
        ty = self.ch(["Nat", "Int", "Bool"])
        t = self.gen(ty, d - 1, env)
        self.pool.setdefault(ty, []).append(t)
        h = self.cmp(ty, t, self.gen(ty, 0, env))
        return f"(({h}) → {self.gen('Prop', d - 1, env)})"

    def cmp(self, ty, a, b):
        if ty in ("Nat", "Int", "String", "Char"):
            op = self.ch(["<", "≤", ">", "≥", "=", "≠"] if ty != "String" else ["<", "=", "≠", ">"])
            return f"{a} {op} {b}"
        return f"{a} {self.ch(['=', '≠'])} {b}"

    def atom(self, d, env):
        dd = max(d - 1, 0)
        if d == 0 and self.coin(0.15):
            return self.ch(["True", "False"])
        ty = self.ch(["Nat", "Nat", "Nat", "Int", "Int", "Int", "Bool", "Bool", "String", "Char", "List Nat",
                      "Option Nat", "Option Int", "Prod", "Pt", "Color", "Tree"])
        if ty == "Bool" and self.coin(0.5):
            return f"({self.gen('Bool', dd, env)} = true)"
        if ty == "List Nat" and self.coin(0.3):
            return f"({self.gen('Nat', dd, env)} ∈ {self.gen('List Nat', dd, env)})"
        a, b = self.gen(ty, dd, env), self.gen(ty, dd, env)
        return f"({self.cmp(ty, a, b)})"

    # ---------------- String / Char ----------------
    def g_String(self, d, env):
        v = self.var(env, "String")
        if d <= 0:
            if v and self.coin(0.6):
                return v
            return self.ch(STR_LITS)
        s = lambda: self.gen("String", d - 1, env)
        opts = [
            lambda: f"({s()} ++ {s()})", lambda: f"(String.append {s()} {s()})",
            lambda: f"(String.push {s()} {self.gen('Char', d-1, env)})",
            lambda: f"(String.singleton {self.gen('Char', d-1, env)})",
            lambda: self.ite("String", d, env),
            lambda: self.match_bool("String", d, env),
        ]
        if "strext" in self.prof:
            opts += [lambda: f"(String.drop {s()} {self.gen('Nat', d-1, env)})",
                     lambda: f"(String.take {s()} {self.gen('Nat', d-1, env)})",
                     lambda: f"(String.mk {self.gen('List Char', d-1, env)})"]
        if v:
            opts += [lambda: v] * 3
        return self.ch(opts)()

    def g_List_Char(self, d, env):
        return f"(String.toList {self.gen('String', d-1, env)})"

    def g_Char(self, d, env):
        v = self.var(env, "Char")
        if d <= 0:
            if v and self.coin(0.6):
                return v
            return self.ch(CHR_LITS)
        opts = [
            lambda: f"(String.get {self.gen('String', d-1, env)} ⟨{self.ch([0, 1, 2])}⟩)",
            lambda: f"((String.get? {self.gen('String', d-1, env)} ⟨{self.ch([0, 1, 2])}⟩).getD {self.gen('Char', 0, env)})",
            lambda: f"(Char.ofNat {self.gen('Nat', d-1, env)})",
            lambda: self.ite("Char", d, env),
            lambda: self.ch(CHR_LITS),
        ]
        if v:
            opts += [lambda: v] * 2
        return self.ch(opts)()

    # ---------------- List Nat ----------------
    def g_List_Nat(self, d, env):
        v = self.var(env, "List Nat")
        if d <= 0:
            if v and self.coin(0.6):
                return v
            return self.ch(LST_LITS)
        l = lambda: self.gen("List Nat", d - 1, env)
        n = lambda: self.gen("Nat", d - 1, env)
        opts = [
            lambda: f"({l()} ++ {l()})", lambda: f"(List.reverse {l()})",
            lambda: f"(List.map (· + {n()}) {l()})", lambda: f"(List.map (fun x => x * 2) {l()})",
            lambda: f"(List.filter (fun x => x % 2 == 0) {l()})",
            lambda: f"(List.filter (· < {n()}) {l()})",
            lambda: f"(List.take {n()} {l()})", lambda: f"(List.drop {n()} {l()})",
            lambda: f"({n()} :: {l()})", lambda: f"(List.tail {l()})",
            lambda: f"(List.replicate ({self.ch([0, 1, 2, 3])} : Nat) {n()})",
            lambda: f"(List.range ({self.ch([0, 1, 2, 3])} : Nat))",
            lambda: f"[{n()}, {n()}]",
            lambda: self.ite("List Nat", d, env),
            lambda: self.match_list("List Nat", d, env),
        ]
        if v:
            opts += [lambda: v] * 3
        return self.ch(opts)()

    # ---------------- Option ----------------
    def g_Option_Nat(self, d, env):
        v = self.var(env, "Option Nat")
        if d <= 0:
            if v and self.coin(0.6):
                return v
            return self.ch(["(none : Option Nat)", f"(some ({self.ch(NAT_LITS)} : Nat))"])
        l = lambda: self.gen("List Nat", d - 1, env)
        n = lambda: self.gen("Nat", d - 1, env)
        o = lambda: self.gen("Option Nat", d - 1, env)
        opts = [
            lambda: f"(some {n()})", lambda: "(none : Option Nat)",
            lambda: f"(List.head? {l()})", lambda: f"(List.getLast? {l()})",
            lambda: f"(Option.map (· + {n()}) {o()})", lambda: f"({l()})[{n()}]?",
            lambda: f"(List.find? (fun x => {n()} < x) {l()})",
            lambda: f"(Option.map Int.toNat {self.gen('Option Int', d-1, env)})",
            lambda: self.ite("Option Nat", d, env),
            lambda: self.match_opt("Option Nat", d, env),
        ]
        if v:
            opts += [lambda: v] * 3
        return self.ch(opts)()

    def g_Option_Int(self, d, env):
        if d <= 0:
            return self.ch(["(none : Option Int)", f"(some ({self.ch(INT_LITS)} : Int))"])
        i = lambda: self.gen("Int", d - 1, env)
        opts = [
            lambda: f"(some {i()})", lambda: "(none : Option Int)",
            lambda: f"(Option.map Int.neg {self.gen('Option Int', d-1, env)})",
            lambda: f"(Option.map Int.ofNat {self.gen('Option Nat', d-1, env)})",
            lambda: self.ite("Option Int", d, env),
        ]
        return self.ch(opts)()

    # ---------------- Prod / user types ----------------
    def g_Prod(self, d, env):
        return f"(({self.gen('Nat', d-1, env)}, {self.gen('Int', d-1, env)}) : Nat × Int)" if d > 0 or self.coin(0.5) \
            else f"(({self.ch(NAT_LITS)} : Nat), ({self.ch(INT_LITS)} : Int))"

    def g_Pt(self, d, env):
        if d <= 0:
            return f"(Pt.mk ({self.ch(NAT_LITS)} : Nat) ({self.ch(INT_LITS)} : Int))"
        opts = [
            lambda: f"(Pt.mk {self.gen('Nat', d-1, env)} {self.gen('Int', d-1, env)})",
            lambda: f"({{ {self.gen('Pt', d-1, env)} with x := {self.gen('Nat', d-1, env)} }} : Pt)",
            lambda: self.ite("Pt", d, env),
        ]
        return self.ch(opts)()

    def g_Color(self, d, env):
        if d <= 0:
            return self.ch(["Color.red", "Color.green", "Color.blue"])
        opts = [lambda: f"(Color.next {self.gen('Color', d-1, env)})", lambda: self.ite("Color", d, env),
                lambda: self.ch(["Color.red", "Color.green", "Color.blue"])]
        return self.ch(opts)()

    def g_Tree(self, d, env):
        if d <= 0:
            return self.ch(["Tree.leaf", "(Tree.node Tree.leaf (1 : Nat) Tree.leaf)"])
        opts = [lambda: f"(Tree.node {self.gen('Tree', d-1, env)} {self.gen('Nat', d-1, env)} {self.gen('Tree', d-1, env)})",
                lambda: "Tree.leaf", lambda: self.ite("Tree", d, env)]
        return self.ch(opts)()

    # ---------------- control ----------------
    def cond(self, d, env):
        if self.coin(0.5):
            return self.gen("Prop", max(d - 1, 0), env)
        return f"{self.gen('Bool', max(d - 1, 0), env)}"

    def ite(self, ty, d, env):
        c = self.cond(d, env)
        return f"(if {c} then {self.gen(ty, d-1, env)} else {self.gen(ty, d-1, env)})"

    def dite(self, ty, d, env):
        a, b = self.gen("Nat", d - 1, env), self.gen("Nat", d - 1, env)
        if ty == "Nat":
            return f"(if _h : {a} < {b} then {b} - {a} else {self.gen(ty, d-1, env)})"
        return f"(if _h : {a} ≤ {b} then {self.gen(ty, d-1, env)} else {self.gen(ty, d-1, env)})"

    def extend(self, env, ty, name):
        e = {k: list(v) for k, v in env.items()}
        e.setdefault(ty, []).append(name)
        return e

    def match_nat(self, ty, d, env):
        disc = self.gen("Nat", d - 1, env)
        k = self.fresh()
        shape = self.r.randint(0, 3)
        if shape == 0:
            return f"(match {disc} with | 0 => {self.gen(ty, d-1, env)} | {k}+1 => {self.gen(ty, d-1, self.extend(env, 'Nat', k))})"
        if shape == 1:
            return (f"(match {disc} with | 1 => {self.gen(ty, d-1, env)} | {k}+1 => {self.gen(ty, d-1, self.extend(env, 'Nat', k))}"
                    f" | 0 => {self.gen(ty, d-1, env)})")
        if shape == 2:
            k2 = self.fresh()
            return (f"(match {disc} with | 0 => {self.gen(ty, d-1, env)} | 2 => {self.gen(ty, d-1, env)}"
                    f" | {k}+3 => {self.gen(ty, d-1, self.extend(env, 'Nat', k))} | {k2} => {self.gen(ty, d-1, self.extend(env, 'Nat', k2))})")
        disc2 = self.gen("Nat", d - 1, env)
        return (f"(match {disc}, {disc2} with | 0, _ => {self.gen(ty, d-1, env)} | _, 0 => {self.gen(ty, d-1, env)}"
                f" | {k}+1, _ => {self.gen(ty, d-1, self.extend(env, 'Nat', k))})")

    def match_int(self, ty, d, env):
        disc = self.gen("Int", d - 1, env)
        k = self.fresh()
        shape = self.r.randint(0, 1)
        if shape == 0:
            return f"(match {disc} with | 0 => {self.gen(ty, d-1, env)} | -1 => {self.gen(ty, d-1, env)} | _ => {self.gen(ty, d-1, env)})"
        return (f"(match {disc} with | Int.ofNat {k} => {self.gen(ty, d-1, self.extend(env, 'Nat', k))}"
                f" | Int.negSucc {k} => {self.gen(ty, d-1, self.extend(env, 'Nat', k))})")

    def match_opt(self, ty, d, env):
        disc = self.gen("Option Nat", d - 1, env)
        k = self.fresh()
        if self.coin(0.5):
            return f"(match {disc} with | none => {self.gen(ty, d-1, env)} | some {k} => {self.gen(ty, d-1, self.extend(env, 'Nat', k))})"
        return (f"(match {disc} with | some 0 => {self.gen(ty, d-1, env)} | some {k} => {self.gen(ty, d-1, self.extend(env, 'Nat', k))}"
                f" | none => {self.gen(ty, d-1, env)})")

    def match_list(self, ty, d, env):
        disc = self.gen("List Nat", d - 1, env)
        a, b, t = self.fresh("a"), self.fresh("b"), self.fresh("t")
        if self.coin(0.5):
            return (f"(match {disc} with | [] => {self.gen(ty, d-1, env)} | [{a}] => {self.gen(ty, d-1, self.extend(env, 'Nat', a))}"
                    f" | {a} :: {b} :: _ => {self.gen(ty, d-1, self.extend(self.extend(env, 'Nat', a), 'Nat', b))})")
        return (f"(match {disc} with | {a} :: {t} => {self.gen(ty, d-1, self.extend(self.extend(env, 'Nat', a), 'List Nat', t))}"
                f" | _ => {self.gen(ty, d-1, env)})")

    def match_bool(self, ty, d, env):
        disc = self.gen("Bool", d - 1, env)
        if self.coin(0.5):
            return f"(match {disc} with | true => {self.gen(ty, d-1, env)} | false => {self.gen(ty, d-1, env)})"
        return f"(match {disc} with | false => {self.gen(ty, d-1, env)} | _ => {self.gen(ty, d-1, env)})"


QTYPES = ["Nat", "Nat", "Nat", "Int", "Int", "Int", "Bool", "String", "List Nat", "Option Nat", "Char"]


def hyp(g, ty, x):
    if ty == "Nat":
        return g.ch([f"{x} < {g.ch([1, 2, 3, 5])}", f"{x} = 0", f"{x} ≠ 0", f"0 < {x}", f"{x} ≤ 1", f"{x} % 2 = 0",
                     f"{x} > {g.ch([1, 2, 3])}"])
    if ty == "Int":
        return g.ch([f"{x} < 0", f"0 ≤ {x}", f"{x} = 0", f"{x} ≠ 0", f"{x} < {g.ch([1, 2, 3])}", f"-3 < {x}",
                     f"{x} * {x} < 10", f"{x} % 2 = 1"])
    if ty == "Bool":
        return g.ch([f"{x} = true", f"{x} = false"])
    if ty == "String":
        return g.ch([f"{x} = \"\"", f"{x} ≠ \"\"", f"{x}.length < 2"])
    if ty == "List Nat":
        return g.ch([f"{x} = []", f"{x} ≠ []", f"{x}.length < 2", f"0 ∈ {x}"])
    if ty == "Option Nat":
        return g.ch([f"{x} = none", f"{x}.isSome", f"{x} = some 0"])
    return g.ch([f"{x} = 'a'", f"{x} ≠ 'a'"])


def make_prop(g, mode, depth):
    g.pool = {}
    if mode == "ground":
        return g.gen("Prop", depth, {}), None
    nv = g.ch([1, 1, 2, 2, 2, 3])
    vs = []
    names = ["x", "y", "z"]
    for j in range(nv):
        vs.append((names[j], g.ch(QTYPES)))
    env = {}
    for n, t in vs:
        env.setdefault(t, []).append(n)
    body = g.gen("Prop", depth, env)
    hs = []
    for n, t in vs:
        if g.coin(0.35):
            hs.append(hyp(g, t, n))
    for h in hs:
        body = f"({h}) → {body}"
    binders = " ".join(f"({n} : {t})" for n, t in vs)
    blast = f"∀ {binders}, {body}"
    small = nv >= 3
    bounded = "".join(f"∀ {n} ∈ {(VAL_LISTS_S if small else VAL_LISTS)[t]}, " for n, t in vs) + body
    return blast, bounded


def main():
    outdir, seed, nprops, mode = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    perfile = int(sys.argv[5]) if len(sys.argv) > 5 else 60
    profile = sys.argv[6] if len(sys.argv) > 6 else ""
    rng = random.Random(seed)
    g = G(rng, profile)
    os.makedirs(outdir, exist_ok=True)
    props = []
    seen = set()
    while len(props) < nprops:
        depth = rng.choice([1, 2, 2, 3, 3, 4]) if mode == "ground" else rng.choice([1, 2, 2, 3])
        p, b = make_prop(g, mode, depth)
        if len(p) > 1500 or p in seen:
            continue
        seen.add(p)
        props.append((p, b))
    header = "import Blaster\nset_option linter.unusedVariables false\n" + PRE + "\n"
    hlines = header.count("\n")
    meta = open(os.path.join(outdir, "props.jsonl"), "a")
    for fi in range(0, len(props), perfile):
        chunk = props[fi:fi + perfile]
        tag = f"{seed}_{fi // perfile}"
        bl, ol = [header], [header.replace("import Blaster\n", "-- oracle\n")]
        for j, (p, b) in enumerate(chunk):
            bl.append(f"#blaster (timeout: 5) (gen-cex: 0) [{p}]\n")
            if mode == "ground":
                ol.append(f"#eval decide ({p})\n")
            else:
                ol.append(f"#eval decide ({b})\n")
            meta.write(json.dumps({"tag": tag, "line": hlines + 1 + j, "mode": mode, "prop": p, "bounded": b}) + "\n")
        open(os.path.join(outdir, f"blast_{tag}.lean"), "w").write("".join(bl))
        open(os.path.join(outdir, f"oracle_{tag}.lean"), "w").write("".join(ol))


if __name__ == "__main__":
    main()
