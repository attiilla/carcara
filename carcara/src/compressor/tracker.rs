use super::DisjointPart;
use std::collections::{HashSet, HashMap};

//stores the information from the clause (i,j) across distinct parts
#[derive(Debug)]
pub(super) struct PartTracker{
    track_data: HashMap<(usize,usize), TrackerData>
}

#[derive(Debug)]
struct TrackerData{
    parts_belonged: HashSet<usize>, //the parts (i, j) belong to
    part_count: HashMap<usize, usize>, //the number of times (i,j) appears in the part k
    pub(crate) inv_index: HashMap<usize, usize>, //the index of (i,j) in the part k
    key: (usize, usize) //the key (i, j)
}

impl PartTracker{
    pub fn new() -> PartTracker{
        PartTracker{
            track_data: HashMap::new()
        }
    }

    pub fn add_step_to_part(&mut self, step: (usize, usize), part: &DisjointPart){
        match &self.track_data.get(&step){
            Some(tracker) => {
                tracker.increase_in_part(part.number);
            }
            None => {
                println!("None found");
                //let mut map = HashMap::new();
                let tracker = TrackerData::new(step, part.number, None);
                self.track_data.insert(step,tracker);
            }
        }
    }

    pub fn set_index_in_part(&mut self, step: (usize, usize), part: &DisjointPart, ind: usize){
        match &self.track_data.get(&step){
            Some(tracker) => tracker.inv_index.insert(part.numb,ind),
            None => panic!("Unexpected behavior\nYou can't set the index of a clause that is not being tracked")
        };
    }

    pub fn parts_containing(&self, step: (usize, usize)) -> Result<Vec<usize>,()>{
        match &self.track_data.get(&step){
            Some(tracker) => Ok(tracker.parts_belonged_ref().iter().cloned().collect()),
            None => Err(())
        }
    }
}

impl TrackerData{
    pub fn new(key: (usize, usize), first_part: usize, ind: Option<usize>) -> TrackerData{
        let parts_belonged: HashSet<usize> = std::iter::once(first_part).collect();
        let part_count: HashMap<usize, usize> = std::iter::once((first_part, 1)).collect();
        let inv_index: HashMap<usize, usize>;
        match ind{
            Some(k) => inv_index = std::iter::once((first_part, k)).collect(),
            None => inv_index = HashMap::new()
        };
        TrackerData{
            parts_belonged,
            part_count,
            inv_index,
            key
        }
    }

    pub fn increase_in_part(&mut self, numb: usize){
        if self.parts_belonged.contains(&numb){
            if let Some(c) = self.part_count.get_mut(&numb) {
                *c += 1;
            } else {
                panic!("Some clause was added to a part but wasn't counted as such");
            }
        } else {
            self.parts_belonged.insert(numb);
            self.part_count.insert(numb,1);
        }
    }

    pub fn parts_belonged_ref(&self) -> &HashSet{
        &self.parts_belonged
    }
}