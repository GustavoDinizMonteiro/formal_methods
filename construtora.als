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
sig Construtora {
	contratos : set Contrato
	
}

sig Contrato {
	construcao : one Construcao
}

abstract sig Construcao {
	pedreiros : one EquipePedreiros,
	pintores : one EquipePintores
}
one sig Predio, CondominioPopular,  Estadio extends Construcao {}

abstract sig Engenheiro {}
sig EngenheiroCivil extends Engenheiro{}
sig EngenheiroEletricista extends Engenheiro{}

abstract sig Equipe {}
sig EquipePedreiros extends Equipe {}
sig EquipePintores extends Equipe {}

///////////////////////////////////////////////.....FATOS......///////////////////////////////////////////////

fact {
	all c : Construtora | some c.contratos
	all c : Contrato | one c.~contratos
	
}

///////////////////////////////////////////////.....ASSERTS......///////////////////////////////////////////////

assert {
	all c : Construtora | #(c.contratos) = 3
}

assert{
	//garantir que o Contrato tenha uma instancia de cada tipo de Construção
	//all c : Contrato | c.construcao
}

pred show(){}

run show for 3	
