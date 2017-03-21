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

///////////////////////////////////////////////.....ASSINATURAS......///////////////////////////////////////////////
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
	pintores : lone EquipePintores,
	pedreiros : some EquipePedreiros,
	engenheiros: lone EquipeEngenheiros	
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

///////////////////////////////////////////////.....FATOS......///////////////////////////////////////////////

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
	one e:EquipePintores | one e.~pintores
}

fact {
	one e:EquipeEngenheiros | one e.~engenheiros
}

fact {
	all c:Construcao | (one c.engenheiros and #(c.pintores)=0) 
				or (#(c.engenheiros)=0 and one c.pintores)
				or (#(c.engenheiros)=0 and #(c.pintores)=0)
}

///////////////////////////////////////////////.....ASSERTS......///////////////////////////////////////////////

assert contrutoraTest{
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

// toda obra possui pelo menos uma equipe de pedreiros trabalhando
assert peloMenosUmaEqPedreirosPorObra{
	all c: Construcao | #(c.pedreiros) > 0
}




/*
Haverá um contrato para construção de um prédio.
Haverá um contrato para construção de um condomínio popular.
Haverá um contrato para construção de um estádio de futebol.
A construtora conta com 4 equipes de pedreiros.
A construtora conta com 1 engenheiro civil
A construtora conta com 1 engenheiro eletricista.
A construtora conta com 1 equipe de pintores.
*/

///////////////////////////////////////////////.....MAIN......///////////////////////////////////////////////


check contrutoraTest for 10

check peloMenosUmaEqPedreirosPorObra for 10


pred show(){}

run show for 5
