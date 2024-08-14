pub enum CompressionError{
    SubproofNotImplementedYet,
    ResolutionError(Vec<(usize,usize)>),
    Collection(CollectionError)
}

pub enum CollectionError{
    NodeWithoutInwardEdge,
}