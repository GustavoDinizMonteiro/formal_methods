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
	pintores : one EquipePintores,
	pedreiros : some EquipePedreiros,
	eCivil : one EngenheiroCivil,
	eEletricista : one EngenheiroEletricista	
}
one sig Predio, CondominioPopular,  Estadio extends Construcao {}

abstract sig Engenheiro {}
sig EngenheiroCivil, EngenheiroEletricista extends Engenheiro{}

abstract sig Equipe {}
sig EquipePedreiros, EquipePintores extends Equipe {}

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
	
	all e:EngenheiroEletricista | one e.~eEletricista
}

fact {
	all e:EquipePintores | one e.~equipePintores
}

fact {
	all c:Construcao | (one c.eCivil and one c.eEletricista) or (#(c.eCivil)=0 and #(c.eEletricista)=0)
	
}

///////////////////////////////////////////////.....ASSERTS......///////////////////////////////////////////////

assert {
	one c : Construtora | #(c.contratos) = 3
}

pred show(){}

run show for 5
