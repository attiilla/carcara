use ahash::{AHashMap, AHashSet};
use crate::ast::*;
use std::collections::VecDeque;
use std::hash::Hash;

// enum listing the compression algorithms used in the compression
//#[derive(Debug)]
//pub enum CompressionAlgorithms{
//    LowerUnits,
//}

// Is essential to have a representation of the proof refered by id, since the standard representation 
// refers to previous steps by its number, and these numbers will certainly change in a successfull compression
pub type IdIndexedProof = AHashMap<String, ProofStepParameters>;
//Everything i used from ProofStep, except it is a hash map
//Does have an extra flag deleted, doesn't have arguments and discharge

#[derive(Clone,Debug)]
pub struct ProofStepParameters{
    pub clause: Vec<Rc<Term> >,
    pub rule: String,
    pub premises: Vec<String>,
    pub deleted: bool
}

impl ProofStepParameters{
    fn new(clause: Vec<Rc<Term> >, rule: String) -> ProofStepParameters{
        let empty_premises: Vec<String> = vec![];
        ProofStepParameters{
            clause,
            rule,
            premises: empty_premises,
            deleted: false
        }
    }
}


#[derive(Debug)]
pub struct Compressor<'a>{
    //keeps a reference to the original proof stored to find the original root
    //the root may be found at any time when a proof is complete by looking for an empty clause
    //but after fix_broken_proof the root will no longer be an empty_clause
    //could have just stored the root_id, but preferred store the original proof because the id and the reference are cheap to store
    //and i though i maybe would need to look to the original proof when shifting back to the previous representation of the proof
    pub original_proof: &'a Proof,
    pub formated_proof: IdIndexedProof,
    
    //needed for reinsert units, could have been stored in the function as a local variable
    //but i thought it would be interesting to be able to get the root at const time
    pub current_root: String,
//    pub compression_steps: Vec<CompressionAlgorithms>,

    //used to name the new nodes created in reinsert_units
    //could have been stored in the function as a local varible
    pub new_node_index: usize
}


impl<'a> Compressor<'a>{
    pub fn id_indexation(p: &Proof) -> IdIndexedProof{
        let mut graph: IdIndexedProof = AHashMap::new();
        let commands_vector = &p.commands;
        for i in commands_vector.iter(){
            match i{
                ProofCommand::Assume{id,term} => {
                    let proof_parameters : ProofStepParameters = ProofStepParameters::new(vec![term.clone()],"Assume".to_string());
                    graph.insert(id.clone(),proof_parameters);
                }
                ProofCommand::Step(s) => {
                    let mut proof_parameters : ProofStepParameters = ProofStepParameters::new(s.clause.clone(),s.rule.clone());
                    let mut premises_by_id: Vec<String> = vec![];
                    for i in 0..s.premises.len(){
                        let premise_position = s.premises[i].1;
                        let id: String = match &commands_vector[premise_position]{
                            ProofCommand::Assume{id,term:_} => id.clone(),
                            ProofCommand::Step(ss) => ss.id.clone(),
                            ProofCommand::Subproof(_) => "subproof".to_string()
                        };
                        premises_by_id.push(id);
                    }
                    proof_parameters.premises = premises_by_id;
                    graph.insert(s.id.clone(),proof_parameters);
                }
                _ => println!("subproof"),//Placeholder for treatment of compression of proofs containing subproofs
            };
        }
        graph
    }

    pub fn new(p: &'a Proof) -> Result<Compressor, &'static str> {
        if Compressor::lower_units_compressible(p){
            Ok(Compressor {
                original_proof: &p,
                formated_proof: Compressor::id_indexation(&p),
                current_root: match &p.commands.last().unwrap(){
                    ProofCommand::Assume{id, ..} => id.to_string(),
                    ProofCommand::Step(s) => s.id.clone(),
                    ProofCommand::Subproof(_) => "subproof".to_string()
                },
                new_node_index: 0,
                //compression_steps: Vec::new(),
                //compression_index: 0
            })
        }
        else{
            Err("Must be LU compressible")
        }
    }

    pub fn lower_units_compressible(p: &Proof) -> bool{
        let n = p.commands.len();
        let command_vector = &p.commands;
        let mut lu_compatible = vec![false; n];
        for i in 0..n{
            if command_vector[i].is_resolution() || command_vector[i].is_assertion(){
                lu_compatible[i] = true;
            }
        }
        lu_compatible.iter().fold(true, |acc, &x| acc && x)
    }

    // Only performs Lower Units at the moment
    pub fn compress(&mut self) -> (){
        let mut units_queue  = self.collect_units();
        self.fix_broken_proof(&self.original_root_id());
        self.reinsert_units(units_queue);
    }

    pub fn fix_broken_proof(
        &mut self, 
        node_id: &String
    ) -> String{
        let children = self.formated_proof.
            get_mut(node_id).
            unwrap().
            premises.
            clone();
        if children.len()<2{    //se não tem premissas, é um assume unário, ou seja, uma "folha" da árvore
                                //se só tem uma premissa, essa premissa é um Assume não unário e portanto não participa de nenhuma resolução
            return node_id.clone();
        }
        let premise_deleted = ( //checo se alguma premissa foi deletada
                                              //nunca ambas terão sido deletadas, pois isso implica em premissas unárias, o que implica que o nó atual é a clausula vazia
                                              //mas as premissas da cláusula vazia nunca são deletadas pela construção da função collect_units
            self.formated_proof.get(&children[0]).unwrap().deleted, 
            self.formated_proof.get(&children[1]).unwrap().deleted
        );
        if (premise_deleted.0 || premise_deleted.1) == false{ //entra nesse if se nenhuma premissa foi deletada
            //chama recursivamente o algoritmos para as 2 premissas
            let ans_left = self.fix_broken_proof(&children[0]); //se algum nó diretamente acima dessa premissa foi deletado, a nova premissa será o nó que não foi deletado
            let ans_right = self.fix_broken_proof(&children[1]);
            let new_conclusion = self.binary_resolution(&ans_left, &ans_right);
            let mut node = self.formated_proof
            .get_mut(node_id)
            .unwrap();
            node.premises = vec![ans_left.clone(),ans_right.clone()]; //atualiza as premissas
            node.clause = new_conclusion;   //atualiza a conclusão
            return node_id.clone();
        } else { //caso alguma premissa foi deletada
            let i: usize;
            if premise_deleted.1{ //i indicará a premissa que não foi deletada
                i = 0;
            } else {
                i = 1;
            }
            //se a premissa restante não tiver nenhum nó diretamente acima deletado, retorna a própria premissa
            //se algum nó acima houver sido deletado, retorna alguma chamada recursiva da função
            let glue = self.fix_broken_proof(&children[i]);
            self.formated_proof.remove(node_id);//deleta o nó atual pois ele será substituífo pelo último nó do "caminho" gerado pelas
                                                //premissas não-deletadas de sua premissa não deletada
            return glue;
        }
    }
    

    //remove pub
    //pub fn recompute_resolutions

    // Working
    // remove pub
    pub fn binary_resolution(&self,node_left: &String, node_right: &String) -> Vec<Rc<Term>>{
        fn remove_duplicates<T: Eq + Hash + Clone>(vec: &mut Vec<T>) {
            let mut set = AHashSet::new();
            let mut i = 0;
        
            while i < vec.len() {
                if !set.insert(vec[i].clone()) {
                    vec.remove(i);
                } else {
                    i += 1;
                }
            }
        }
        let mut terms_left = self.formated_proof.get(node_left).unwrap().clause.clone();
        let mut terms_right = self.formated_proof.get(node_right).unwrap().clause.clone();
        let pivot: (usize, usize) = self.find_pivot(&terms_left, &terms_right);
        terms_left.remove(pivot.0);
        terms_right.remove(pivot.1);
        terms_left.extend(terms_right);
        remove_duplicates(&mut terms_left);
        terms_left
    }
    //Working
    //remove pub
    pub fn find_pivot(&self,terms_left: &Vec<Rc<Term>>, terms_right: &Vec<Rc<Term>>) -> (usize, usize){
        fn compare_possible_pivot(p: (u32, &Rc<Term>), q: (u32, &Rc<Term>)) -> bool{
            // check if the literals are distinct && compares how many not they have to see if they can  be used as pivot
            if (p.1==q.1)&&(p.0%2!=q.0%2){
                return true;
            }
            false
        }
        
        let non_negated_terms_left: Vec<(u32, &Rc<Term>)> = terms_left.iter().map(|term| term.remove_all_negations()).collect();
        //println!("non_negated_terms_left: {:?}",non_negated_terms_left);
        
        let non_negated_terms_right: Vec<(u32, &Rc<Term>)> = terms_right.iter().map(|term| term.remove_all_negations()).collect();
        //println!("non_negated_terms_right: {:?}",non_negated_terms_right);

        let aux_set: AHashSet<(u32, &Rc<Term>)> = non_negated_terms_left.clone().into_iter().collect();
        let pivot = non_negated_terms_right.iter().find(|&x| 
                                                    aux_set.iter().any(|&y| 
                                                            compare_possible_pivot(*x,y))).unwrap();
        //println!("compare: {:?}",compare_possible_pivot(non_negated_terms_left[0], non_negated_terms_right[0]));
        //println!("termos: {:?}; {:?}",&non_negated_terms_left[0].1, &non_negated_terms_right[0].1);
        //println!("comparação direta: {:?}",non_negated_terms_left[0].1==non_negated_terms_right[0].1);
        //println!("pivot: {:?}",pivot);
        let position_left = non_negated_terms_left.iter().position(|(_, item)| *item == pivot.1).unwrap();
        let position_right = non_negated_terms_right.iter().position(|(_, item)| *item == pivot.1).unwrap();
        (position_left, position_right)
    }

    pub fn original_root_id(&self) -> String{
        match self.original_proof.commands.last().unwrap(){
            ProofCommand::Assume{id, ..} => id.to_string(),
            ProofCommand::Step(s) => s.id.clone(),
            ProofCommand::Subproof(_) => "subproof".to_string()
        }
    }

    // Working
    // remove pub
    pub fn collect_units(&mut self) -> VecDeque<(String,ProofStepParameters)>{
        let mut clause_len;
        let mut units_queue: VecDeque<(String,ProofStepParameters)> = VecDeque::new();
        let mut bfs_queue: VecDeque<String> = VecDeque::new();
        let mut visited: AHashSet<String> = AHashSet::new();
        let root_id = match self.original_proof.commands.last(){
            None => panic!("This proof doesn't have any commands"),
            Some(ProofCommand::Assume{id,..}) => id.clone(),
            Some(ProofCommand::Step(s)) => s.id.clone(),
            Some(ProofCommand::Subproof(..)) => panic!("Subproof handling not implemented yet")
        };
        let mut root_and_premises = self.formated_proof.get(&root_id).unwrap().premises.clone();
        root_and_premises.push(root_id.clone());
        let mut current_node = Some(root_id);
        while let Some(s) = current_node{  
            if visited.contains(&s[..]) {
              current_node = bfs_queue.pop_front();
            } else {
                // Checks if the rule used to derive this node is "or"                //IMPORTANTE
                // If it is "or", don't put the childs of the node in the queue         Regra or transforma uma aplicação de operador or em uma cláusula
                                                                                      //Não pode ser resolvida
                if &self.formated_proof.get(&s).unwrap().rule!="or"{
                    //Put the childs of the current_node on the search queue
                    for i in &self.formated_proof.get(&s).unwrap().premises{
                        bfs_queue.push_back(i.to_string());
                    }
                }
                // Checks if the current_node can get closer to the proof root
                if !root_and_premises.contains(&s){
                    // Checks if the clause of the node is unitary
                    clause_len = self.formated_proof.get(&s).unwrap().clause.len();
                    if clause_len==1{
                        self.formated_proof.get_mut(&s).unwrap().deleted = true;
                        let node_data = self.formated_proof.get(&s).unwrap().clone();
                        let mut switch = false;
                        for i in &node_data.premises{
                            //IMPORTANTE
                            //Checa se alguma premissa do nó atual já está na fila
                            //em caso afirmativo, retorna sua posição e adiciona o nó atual na fila antes de sua premissa 
                            let early_child = units_queue.iter().position(|(node_id, _)| node_id==i);
                            match early_child{
                                None => (),
                                Some(u) => {
                                    println!("u vale {}",u);
                                    units_queue.insert(u,(s.clone(),node_data.clone()));
                                    switch = true;
                                },
                            }
                        }
                        if !switch{
                            units_queue.push_back((s.clone(),node_data.clone()));
                        }
                        
                    }
                }
                visited.insert(s.clone());
                current_node = bfs_queue.pop_front();
            }
        }
        units_queue
    }


    pub fn reinsert_units(&mut self, mut queue: VecDeque<(String,ProofStepParameters)>) -> (){
        while queue.len()!=0{
            let to_reinsert = queue.pop_front().unwrap().0;
            self.formated_proof.get_mut(&to_reinsert).unwrap().deleted = false;
            let new_node_data = ProofStepParameters{
                clause: self.binary_resolution(&self.current_root,&to_reinsert),
                rule: String::from("resolution"),
                premises: vec![self.current_root.clone(),to_reinsert],
                deleted: false
            };
            let new_node_id = format!("n{}",self.new_node_index);
            self.new_node_index+=1;
            self.formated_proof.insert(new_node_id.clone(),new_node_data);
            self.current_root = new_node_id;
        }
    }
}

/*#[cfg(test)]
mod test{
    use super::*;
    #[test]
    fn test_binary_resolution(c: Compressor){

    }
}*/


//Descrever as adaptações do algoritmo para funcionar para resolução n-ária formalmente como no artigo
//Rever e explicar as decisões de projeto a respeito da representação do grafo no algoritmo
//Explicar com detalhes a implementação do algoritmo