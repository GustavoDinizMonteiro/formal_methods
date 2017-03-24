/*
Tema 8: Construtora de prédios

Uma construtora na cidade de Campina Grande está com 3 contratos assinados para construir um prédio, 
um condomínio popular e um estádio de futebol. Para isso eles contam com 4 equipes de pedreiros, 
2 engenheiros cada um com uma especialidade(um engenheiro civil, um engenheiro eletricista) e 
1 equipe de pintores. Como as obras são demoradas e grandes os dois engenheiros trabalham sempre juntos,
 a equipe de pintores não trabalha na mesma obra dos engenheiros e sempre as obras tem, pelo menos, 
uma equipe de pedreiros que varia ao longo do tempo, para não ficarem sempre na mesma obra.

A construtora terá 3 contratos.
Haverá um contrato para construção de um prédio.
Haverá um contrato para construção de um condomínio popular.
Haverá um contrato para construção de um estádio de futebol.
A construtora conta com 4 equipes de pedreiros.
A construtora conta com 1 engenheiro civil
A construtora conta com 1 engenheiro eletricista.
A construtora conta com 1 equipe de pintores.

Constranges:
Os dois engenheiros sempre trabalham juntos.
A equipe de pintores não trabalha na mesma hora que os engenheiros.
Toda obra tem pelo menos uma equipe de pedreiros.
Uma equipe de pedreiros varia de obra ao longo do tempo.

Integrantes: Daniyel Rocha, Gustavo Diniz, Matheus Procópio, Vinicius Agostini
Cliente: Gileade
*/

module construtora

open util/ordering[Time]

-------------------------------------ASSINATURAS-------------------------------------
sig Time {}

one sig Construtora {
	contratos : set Contrato,
	equipePedreiros : some EquipePedreiros,
	engenheiroCivil : one EngenheiroCivil,
	engenheiroEletricista : one EngenheiroEletricista,
	equipePintores : one EquipePintores
}

sig Contrato {
	construcao : one Construcao
}

abstract sig Construcao {
	pintores : EquipePintores lone -> Time,
	pedreiros : EquipePedreiros some -> Time,
	engenheiros: EquipeEngenheiros lone -> Time	
}
one sig Predio, CondominioPopular,  Estadio extends Construcao {}

abstract sig Engenheiro {}
sig EngenheiroCivil, EngenheiroEletricista extends Engenheiro{}

one sig EquipeEngenheiros {
	civil: one EngenheiroCivil,
	eletricista: one EngenheiroEletricista
}

abstract sig Equipe {}
sig EquipePedreiros extends Equipe {}
one sig EquipePintores extends Equipe {}

-------------------------------------FATOS-------------------------------------

fact invariantesConstrutora	{
	// Toda construtora possui 3 contratos
	all c : Construtora | #(c.contratos) = 3
	// Todos os contratos estão atrelados a uma unica construtora
	all c : Contrato | one c.~contratos	
}

fact invariantesContrato{
	// Todos os predios estão atrelados a apenas um contrato
	all c:Predio | one c.~construcao
	// Todos os condominios populares estão atrelados a apenas um contrato
	all c:CondominioPopular | one c.~construcao
	// Todos os estadios estão atrelados a apenas um contrato
	all c:Estadio | one c.~construcao
}

fact invariantesEquipePedreiros{
	// Existem apenas 4 equipes de pedreiros
	#(EquipePedreiros) = 4
	// Todos as equipes de pedreiros estão atreladas a apenas uma construtora
	all e:EquipePedreiros | one e.~equipePedreiros
	// Em qualquer tempo, para qualquer equipe de pedreiros, uma equipe estará atrelada a apenas uma construcao
	all t: Time | (all e: EquipePedreiros | one e.~(pedreiros.t))
}

fact invariantesEquipeEngenheiros{
	// Todos os engenheiros civis estão atrelados a apenas uma construtora	
	all e:EngenheiroCivil | one e.~engenheiroCivil
	// Todos os engenheiros eletricistas estão atrelados a apenas uma construtora	
	all e:EngenheiroEletricista | one e.~engenheiroEletricista
	// Em qualquer tempo, para qualquer equipe de engenheiros, uma equipe estará atrelada a apenas uma construcao
	all t: Time - first | (one e: EquipeEngenheiros | one e.~(engenheiros.t))
}

fact invariantesEquipePintores{
	// Todas as equipes de pintores estão atreladas a apenas uma construtora
	one e:EquipePintores | one e.~equipePintores
	// Em qualquer tempo, para qualquer equipe de pintores, uma equipe estará atrelada a apenas uma construcao
	all t: Time - first | (one e: EquipePintores | one e.~(pintores.t))
}

fact relacaoPintoresEEngenheiros{
	// Não há construcao que possua engenheiros e pintores
	no c:Construcao | #(c.engenheiros) > 0 and #(c.pintores) > 0
}



fact traces {
	init[first]
	all pre: Time-last | let pos = pre.next | 

	some c1:Construcao, c2: Construcao - c1, ep: EquipePintores, ee:EquipeEngenheiros | 
		alocaEqPintores[c1, ep, pre, pos] or 
		desalocaEqPintores[c1, ep, pre, pos] or 
		alocaEqEngenheiros[c1, ee, pre, pos] or 
		variaEqPedreiros[c1, c2, pre, pos]

}

-------------------------------------PREDICADOS-------------------------------------

pred init [t: Time]{
	// No tempo t, a equipe de pintores não está atrelada a qualquer obra
	all c: Construcao | no (c.pintores).t 
	// No tempo t, a equipe de engenheiros não está atrelada a qualquer obra
	all c: Construcao | no (c.engenheiros).t
}

pred alocaEqPintores[c:Construcao, ep:EquipePintores, t: Time, t':Time]{
	ep !in getPintores[c, t]
	(c.pintores).t' = getPintores[c, t] + ep
}

pred desalocaEqPintores[c:Construcao, ep:EquipePintores, t: Time, t':Time]{
	ep in getPintores[c, t]
	(c.pintores).t' = getPintores[c, t] - ep
}

pred alocaEqEngenheiros[c:Construcao, ee:EquipeEngenheiros, t: Time, t':Time]{
	ee !in getEngenheiros[c, t]
	(c.engenheiros).t' = getEngenheiros[c, t] + ee
}

pred variaEqPedreiros[c1:Construcao, c2:Construcao, t: Time, t':Time]{
	c1.pedreiros.t' =  getPedreiros[c2, t]
	c2.pedreiros.t' = getPedreiros[c1, t]
}


-------------------------------------FUNÇÕES-------------------------------------

fun getPedreiros[c1: Construcao, t: Time] : set EquipePedreiros{
	c1.pedreiros.t
}

fun getEngenheiros[c1: Construcao, t: Time] : set EquipeEngenheiros{
	c1.engenheiros.t
}

fun getPintores[c1: Construcao, t: Time] : set EquipePintores{
	c1.pintores.t
}

-------------------------------------ASSERTS-------------------------------------


assert construtoraTest{
	// Só existe uma construtora.
	#(Construtora) = 1

	// A construtora terá 3 contratos.
	all c : Construtora | #(c.contratos) = 3

	//A construtora conta com 4 equipes de pedreiros.
	all c: Construtora | #(c.equipePedreiros)=4

	//A construtora conta com 1 engenheiro civil
	all c: Construtora | #(c.engenheiroCivil) = 1	

	//A construtora conta com 1 engenheiro eletricista.
	all c: Construtora | #(c.engenheiroEletricista) = 1	

	//A construtora conta com 1 equipe de pintores.
	all c: Construtora | #(c.equipePintores) = 1
}


assert contratoTest{
	// Existem tres contratos
	#(Contrato) = 3

	//Haverá um contrato para construção de um prédio.
	#(Predio) = 1

	//Haverá um contrato para construção de um condomínio popular.
	#(CondominioPopular) = 1

	//Haverá um contrato para construção de um estádio de futebol.
	#(Estadio) = 1
}

assert construcaoTest{
	// sempre as construcoes tem, pelo menos, uma equipe de pedreiros
	all c: Construcao, t: Time | #(c.pedreiros.t) > 0
	
	//os dois engenheiros trabalham sempre juntos
		//somente uma construcao possui uma equipe de engenheiros
		all c:Construcao, t: Time | #(c.engenheiros.t)=1 or #(c.engenheiros.t)=0 
		//existe apenas uma equipe de engenheiros
		#(EquipeEngenheiros) = 1
		//a unica equipe de engenheiros existente eh composta por um engenheiro civil e um eletricista
		all ee:EquipeEngenheiros | #(ee.civil) = 1 and #(ee.eletricista) = 1

	//a equipe de pintores nunca trabalha na mesma obra que os engenheiros
	all c:Construcao, t: Time | ( #(c.engenheiros.t)=1 and #(c.pintores.t)=0) 
				or (#(c.engenheiros.t)=0 and #(c.pintores.t)=1 )
				or (#(c.engenheiros.t)=0 and #(c.pintores.t)=0)

}



-------------------------------------MAIN-------------------------------------


check construtoraTest for 10

check contratoTest for 10

check construcaoTest for 10


pred show(){}

run show for 30
