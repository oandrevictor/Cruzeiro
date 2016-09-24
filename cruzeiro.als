module Cruzeiro 
	// asserts	
	// coisos temporal

	open util/ordering[Time]
	sig Time {}
	
	one sig Cruzeiro{atividadesDisponiveis: set Atividade->Time}

	abstract sig Atividade{}
	abstract sig AtividadeMatutina extends Atividade{}
	abstract sig AtividadeVespertina extends Atividade{}
	abstract sig AtividadeNoturna extends Atividade{}
	
	one sig TorneioDamas extends AtividadeMatutina{}
	one sig Squash extends AtividadeMatutina{}
	one sig AulaNatacao extends AtividadeMatutina{}
	one sig NadoSincronizado extends AtividadeMatutina{}
	one sig Hoquei extends AtividadeVespertina{}
	one sig Meditacao extends AtividadeVespertina{}
	one sig Cinema extends AtividadeVespertina{}
	one sig DegustacaoVinhos extends AtividadeNoturna{}
	one sig Discoteca extends AtividadeNoturna{}

	abstract sig Pessoa{
		participa: set Atividade -> Time
	}

	sig Pai extends Pessoa{}
	sig Mae extends Pessoa{}
	sig FilhaAdolescente extends Pessoa{}
	sig FilhoCrianca extends Pessoa{}
	
	/* Para o desenvolvimento do projeto, levamos como base as especificações da família */
	fact especificacao_familia{
		#Pai = 1
		#Mae = 1
		#FilhaAdolescente = 1
		#FilhoCrianca = 1
	}

	fun pais: set Pessoa{
		(Mae + Pai)		
	}
	fun homens: set Pessoa{
		Pai+ FilhoCrianca
	}

	/* !!!!!!!! Sera que é melhor definir lets? !!!!!!!!!!!!!!! */
	fun manha: one Time{
		first.next
	}
	fun tarde: one Time{
		manha.next
	}
	fun noite: one Time{
		tarde.next
	}

	/* obtem os eventos participados em um horario especifico */
	fun participou_de_manha[p:Pessoa] : set Atividade{
		p.participa.manha
	}
	fun participou_de_tarde[p:Pessoa]: set Atividade{
		p.participa.tarde - participou_de_manha[p]
	}
	fun participou_de_noite[p:Pessoa]: set Atividade{
		p.participa.noite - p.participa.tarde
	}

	pred e_homem[p:Pessoa]{
		p in homens
	}
	
	pred pais_em_atividade[a:Atividade]{
		some p:pais, t:Time| a in p.participa.t
	}

	fact minimo_de_atividades{	
		let noite =  first.next.next.next | all p:Pessoa| #((p.participa).noite) >= 4
	}

	/* O filho não participa de atividades noturnas e requer a presença de um dos pais para toda atividade que participar. */
	fact restricoes_crianca{
		all c:FilhoCrianca, t:Time, a:c.participa.t|
				pais_em_atividade[a]
	}
	fact{
		all c:FilhoCrianca| #{participou_de_noite[c]} = 0
	}

	/* Restricoes Referente ao nado sincronizado */
	fact natacao_e_nado_sincronizado_sao_simultaneos{
		all p:Pessoa, t:Time |let ns =NadoSincronizado, nt= AulaNatacao| !((ns in (p.participa).t) and (nt in (p.participa).t))
	}
	fact homem_nao_participa_de_nado_sincronizado{
		all p:Pessoa, t:Time |let ns =NadoSincronizado|  !(e_homem[p] and (ns in p.participa.t))
	}
	
		
	fact definir_programacao{
		one cruzeiro: Cruzeiro | let noite = tarde.next{
			cruzeiro.atividadesDisponiveis.manha  =  AtividadeMatutina and
			cruzeiro.atividadesDisponiveis.tarde = AtividadeVespertina and
			cruzeiro.atividadesDisponiveis.noite = AtividadeNoturna
			}
	}

	/* inicialização do sistema	*/
	pred init[t:Time]{
		no (Pessoa.participa).t
	}

	/* Adicao de atividades de acordo com o tempo */
	pred participa_atividade[p:Pessoa, a: some Atividade,t,t':Time]{
		(a !in(p.participa).t) and (a in (Cruzeiro.atividadesDisponiveis.t'))  and
		 (((p.participa).t ) in ((p.participa).t')) and (a in ((p.participa).t')) 
	}

	/* É possivel também que em um certo momento, uma pessoa não participe de nenhuma atividade.*/
	pred nao_participa_atividade[p:Pessoa,a: some Atividade,t,t':Time]{
		(a !in(p.participa).t) and (a !in(p.participa).t') or 
		(a in(p.participa).t) and (a in(p.participa).t') 
	}

	/* Execucao Principal. Aqui garantimentos que em todo tempo(exceto o inicial, separado para a inicialização	
	do sistema), toda pessoa tem a oportunidade de participar das atividades (levando em consideração as restrições	
	previamente estabelecidas */
	fact traces{
		init[first]
		all pre: Time - last | 
			let pos = pre.next |
			all  p:Pessoa| 
			all a:Atividade| 
					(participa_atividade[p,a,pre,pos]) or (nao_participa_atividade[p,a,pre,pos])
	}

	pred show[]{
	}

	run show for 10 but 4 Time // Tempo inicial, Manhã, Tarde e Noite
