/*
Tema 8: Construtora de prédios

Uma construtora na cidade de Campina Grande está com 3 contratos assinados para construir um prédio, 
um condomínio popular e um estádio de futebol. Para isso eles contam com 4 equipes de pedreiros, 
2 engenheiros cada um com uma especialidade(um engenheiro civil, um engenheiro eletricista) e 
1 equipe de pintores. Como as obras são demoradas e grandes os dois engenheiros trabalham sempre juntos,
 a equipe de pintores não trabalha na mesma obra dos engenheiros e sempre as obras tem, pelo menos, 
uma equipe de pedreiros que varia ao longo do tempo, para não ficarem sempre na mesma obra.

Integrantes: Daniyel Rocha, Gustavo Diniz, Matheus Procópio, Vinicius Agostini
Cliente: Gileade
*/

module construtora

--Assinaturas
sig Construtora {
	contratos : set Contrato
}

sig Contrato {
	contrucao : one Construcao
}

abstract sig Construcao {}
sig Predio extends Construcao {}
sig CondominioPopular extends Construcao {}
sig Estadio extends Construcao {}

abstract sig Equipe {}
sig EquipePedreiros extends Equipe {}
sig EquipePintores extends Equipe {}

fact {
	all construtora:Construtora | #(construtora.contratos) = 3
	all contrato:Contrato | one contrato.~contratos
}

pred show(){}

run show for 3	
