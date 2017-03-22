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
	pedreiros : some EquipePedreiros,
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

fact {
	all c : Construtora | #(c.contratos) = 3
	all c : Contrato | one c.~contratos	
}

fact {
	all c:Predio | one c.~construcao
	all c:CondominioPopular | one c.~construcao
	all c:Estadio | one c.~construcao
}

fact {
	#(EquipePedreiros) = 4
	all e:EquipePedreiros | one e.~equipePedreiros
	all e:EquipePedreiros | one e.~pedreiros
}

fact {
	all e:EngenheiroEletricista | one e.~engenheiroEletricista
	all e:EngenheiroCivil | one e.~engenheiroCivil
}

fact {
	one e:EquipePintores | one e.~equipePintores
	--one e:EquipePintores | one e.~pintores
}

fact {
	--one e:EquipeEngenheiros | one e.~engenheiros
}

fact {
	no c:Construcao | #(c.engenheiros) > 0 and #(c.pintores) > 0
}

fact{
	//para quaisquer duas construcoes diferentes no mesmo tempo, se uma equipe de pintores estiver em uma determinada construcao, 
	// entao ela nao podera estar na outra construcao.
	all c1 : Construcao, c2: Construcao - c1, e: EquipePintores, t: Time | (e in c1.pintores.t) => (e !in c2.pintores.t) 
	all c1 : Construcao, c2: Construcao - c1, e: EquipeEngenheiros, t: Time | (e in c1.engenheiros.t) => (e !in c2.engenheiros.t)  
}


fact traces {
	init[first]
	all pre: Time-last | let pos = pre.next |

	some c:Construcao, ep: EquipePintores, ee:EquipeEngenheiros | 
		addEqPintores[c, ep, pre, pos] or addEqEngenheiros[c, ee, pre, pos]

}

-------------------------------------PREDICADOS-------------------------------------

pred init [t: Time]{
	one (Construcao.pintores).t
	one (Construcao.engenheiros).t
}

pred addEqPintores[c:Construcao, ep:EquipePintores, t: Time, t':Time]{
	ep !in (c.pintores).t
	(c.pintores).t' = (c.pintores).t + ep
}

pred addEqEngenheiros[c:Construcao, ee:EquipeEngenheiros, t: Time, t':Time]{
	ee !in (c.engenheiros).t
	(c.engenheiros).t' = (c.engenheiros).t + ee
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
	all c: Construcao | #(c.pedreiros) > 0
	
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

run show for 15
