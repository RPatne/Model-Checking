
module SimpleCofMachine
open util/ordering [Cof] as CO
open util/integer as INT
abstract sig CofState{}
one sig Reset, Coin, Coffee, Change extends CofState{}
abstract sig OP{}
one sig ENTER1PCOIN, ENTER2PCOIN,PUSHCOF, PUSHCHANGE, RESET extends OP{}
abstract sig CofType{}
one sig Cof1 extends CofType {}
sig Cof{
	balance: one Int,
	state: one CofState,
	op: OP,
	dispenser: lone CofType
}
// Give us a quick example
pred show1[c: Cof]{}
run show1
pred enter2pcoin[c,c':Cof]{
c.state=Reset &&
c'.balance=INT/add[c.balance,int(2)] &&
c'.dispenser=c.dispenser &&
c'.state=Coin
}
pred enter1pcoin[c,c':Cof]{
c.state=Reset &&
c'.balance=INT/add[c.balance,int(1)] &&
c'.dispenser=c.dispenser &&
c'.state=Coin
}
pred buycof[c,c':Cof]{
c.state=Coin &&
INT/gte[c.balance,int(1)] &&
c'.balance=INT/sub[c.balance,int(1)] &&
no c.dispenser &&
c'.dispenser=Cof1
c'.state=Coffee
}
pred askchange[c,c':Cof]{
c.state=Coffee
INT/gt[c.balance,0] &&
INT/zero[c'.balance] &&
c'.dispenser=c.dispenser &&
c'.state=Change
}
pred reset[c,c':Cof]{
c.state=Change &&
c'.balance=c.balance&&
c'.dispenser=c.dispenser &&
c'.state=Reset
}
pred reset2[c,c':Cof]{
c.state=Coffee &&
c.balance=0 &&
c'.balance=c.balance &&
c'.dispenser=c.dispenser &&
c'.state=Reset
}
pred init[c:Cof]{
c.balance=0 &&
c.state=Reset &&
c.dispenser=none
}
pred traces{
init[CO/first[]] &&
all c:Cof-CO/last[] | let c'= CO/next[c]|((enter1pcoin[c,c'] && c'.op=ENTER1PCOIN)
or
(enter2pcoin[c,c'] && c'.op=ENTER2PCOIN)
or
(buycof[c,c'] && c'.op=PUSHCOF)
or
(askchange[c,c'] && c'.op=PUSHCHANGE)
or
(reset2[c,c'] && c'.op=RESET)
or
(reset[c,c'] && c'.op=RESET))
}
pred transaction{
traces &&
(CO/last[]).op=RESET &&
RESET !in(Cof-CO/last[]).op
}
one sig Goal{goals:set CofState} {goals=Coffee}
one sig Subgoals{subgoals: set CofState} {subgoals=Change}
assert goalsmet {
transaction => let m=CO/max[state.(Goal.goals)]|
some m=> all sg:Subgoals.subgoals|state.sg in CO/prevs[m]
}
// This generates a counterexample with 5
check goalsmet for 5


