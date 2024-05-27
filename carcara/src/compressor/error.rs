pub enum CompressionError{
    Collection(CollectionError),
    SubproofNotImplementedYet,
    ResolutionError(Vec<(usize,usize)>)
}

pub struct CollectionError{
    pub subproofs_to_compress: Vec<Vec<usize>>
}
