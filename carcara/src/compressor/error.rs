pub enum CompressionError{
    Collection(CollectionError),
    SubproofNotImplementedYet,
    ResolutionError(Vec<(usize,usize)>)
}

pub struct CollectionError;
