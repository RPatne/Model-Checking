//Illustrating a Simple Coffee machine Model
module SimpleCofMachine

//Library module used to define a trace of operations by declaring various states
open util/ordering[Cof] as CO

//Signature declaration for set of possible states of coffee machine called CofState
abstract sig CofState{}
//signature declaration for the various states of CofState must be either Initial or Wait
one sig Initial, Wait extends CofState{}

//signature declaration for set of  customer action called OP
abstract sig OP{}
//signature declaration for various actions to initiate changes in the state of coffee machine
one sig Coini, Cofb, Stopb, Coino, Cofo extends OP {}

//signature declaration for Cof to hold the state of coffee machine at one instance in time
sig Cof {
	state: one CofState,
	op: OP
}
//an empty predicate which will run to generate instances
pred show1[c:Cof] {}
//Executing the run command shows the solution to the model
run show1

/*Predicates used to represent operation on coffee machine and 
describe relationship between two instances of Cof signature
*/

pred entercoin[c,c':Cof] { /*It constrains the state before selecting the coffee(c) and 
						after collecting Coffee(c') */

	c.state=Initial && //Ensures that coffee machine is in Initial state initially
	c'.state=Wait // Ensures that coffee machine is in Wait state afterwards

}

pred buycof[c,c':Cof] {
	c.state=Wait &&
	c'.state=Initial
}

pred askchange[c,c':Cof] {
	c.state=Wait &&
	c'.state=Initial
}

pred initial[c:Cof] {
c.state=Initial
}

//predicated describing the valid traces in the system
pred traces {

	initial[CO/first[]] && //initial condition holds for the initial time step

	all c:Cof-CO/last[] | let c'=CO/next[c] | /*for all subsequent times the machine must change
									 in accordance with one of the predicates*/
	
	((entercoin[c,c'] && c'.op=Coini) //action of the customer for entering the input coin
	or
	(buycof[c,c'] && c'.op=Cofb && c'.op = Cofo)/*action of thecustomer to press the coffee button and
										 get the coffee output*/
	or
	(askchange[c,c'] && c'.op=Stopb && c'.op=Coino))/*action of the customer to stop the button and
												get back the coin output*/

}

/*Defining the sequence of events that represent a single interaction of customer with coffee machine
Transaction is referred to as single interaction*/
pred transaction{

	traces && //consists of traces that begin with the initial state
	(CO/last[]).state=Initial &&
	Initial !in (Cof-CO/last[]).state /*finishes with the machine resetting for the one and 
								only one time in that transaction*/

}

//mechanism for representing the Goal and the Subgoal
one sig AchieveCoffee{goals: set OP} {goals=Cofo}
one sig RetrieveChange{subgoals: set OP } { subgoals=Coino}

//For all valid transaction subgoals(sg) must occur in state before the state in which goal(m) occurs
assert DynamicBehaviour{
	transaction => let m=CO/max[op.(AchieveCoffee.goals)] |
	some m => all sg: RetrieveChange.subgoals | op.sg in CO/prevs[m]
}

//Asks the alloy to provide counterexample violating the Assertion for a scope of 5
check DynamicBehaviour for 5
