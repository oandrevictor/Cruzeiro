module cruzeiro

abstract sig Atividade{
}

abstract sig AtividadeMatutina extends Atividade{}
abstract sig AtividadeVespertina extends Atividade{}
abstract sig AtividadeNoturna extends Atividade{}
//Sera que e necessario todas essas assinaturas?
one sig TorneioDamas extends AtividadeMatutina{}
one sig Squash extends AtividadeMatutina{}
one sig AulaNatacao extends AtividadeMatutina{}
one sig NadoSincronizado extends AtividadeMatutina{}
one sig Hoquei extends AtividadeVespertina{}
one sig Meditacao extends AtividadeVespertina{}
one sig Cinema extends AtividadeVespertina{}
one sig DegustacaoVinhos extends AtividadeNoturna{}
one sig Discoteca extends AtividadeNoturna{}

abstract sig Pessoa{participa: set Atividade}
abstract sig Adulto extends Pessoa{filhos: set Filho}
one sig Mae in Adulto{}
one sig Pai in Adulto{}
abstract sig Filho extends Pessoa{
	mae: one Mae,
	pai: one Pai
}
one sig Crianca in Filho {}
one sig Adolescente in Filho{}

fact { all a:Adulto, f:a.filhos | f.pai = a or f.mae = a}
fact{ all f:Filho, p:f.pai, m:f.mae| f in p.filhos and f in m.filhos}
fact criancaForaDeAtividadeNorturna{
	no a:AtividadeNoturna, c:Crianca | a in c.participa 
}
fact crianEAdolescenteSaoPessoasDiferentes{	all c:Crianca,a:Adolescente| c != a
}
fact todoAdultoTemFilho{	all a:Adulto | some c:Crianca | c.pai = a or c.mae =a}
fact CriancaTemPaiEMae{	all c:Crianca | c.mae != c.pai}

fact criancaAcompanhada{
	all c:Crianca,m:c.mae,p:c.pai,a:c.participa| a in m.participa or a in p.participa
}

pred show[]{
	#Pessoa =4
	#Adulto =2
	#Mae =1
	#Pai =1
	#Crianca =1
	#Adolescente =1
	all p:Pessoa| #(p.participa) >= 4}

run show for 6
