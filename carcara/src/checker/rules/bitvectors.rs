use crate::{
    ast::{pool::TermPool, Constant, IndexedOperator, Operator, Rc, Sort, Term},
    checker::rules::assert_clause_len,
};

use super::{assert_eq, RuleArgs, RuleResult};

fn build_term_vec(term: &Rc<Term>, size: usize, pool: &mut dyn TermPool) -> Vec<Rc<Term>> {
    let term = if let Some((Operator::BvBbTerm, args_x)) = term.as_op() {
        args_x.to_vec()
    } else {
        (0..size)
            .map(|i| {
                pool.add(Term::IndexedOp {
                    op: IndexedOperator::BvBitOf,
                    op_args: vec![Constant::Integer(i.into())],
                    args: vec![term.clone()],
                })
            })
            .collect()
    };
    term
}

// pub fn value(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
//     assert_clause_len(conclusion, 1)?;
//     let (v, res_args) = match_term_err!((= v (bbterm ...)) = &conclusion[0])?;


//     match v.as_bitvec() {
//        Some((m, w)) => ...
//        _ => ...
//    }

//     if let Some((m, w)) = v.as_bitvec() {

//         return Ok(());
//     }
// }

pub fn and(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvand x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
          pool,
          (and {x[i].clone()} {y[i].clone()})
        )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}

pub fn or(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvor x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
          pool,
          (or {x[i].clone()} {y[i].clone()})
        )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}


pub fn xor(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvxor x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
          pool,
          (xor {x[i].clone()} {y[i].clone()})
        )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}


pub fn xnor(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvxnor x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
          pool,
          (= {x[i].clone()} {y[i].clone()})
        )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}


pub fn not(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (x, res) = match_term_err!((= (bvnot x) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
          pool,
          (not {x[i].clone()})
        )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}

pub fn ult(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvult x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let mut expected_res = build_term!(pool, (and (not {x[0].clone()}) {y[0].clone()}));

    for i in 1..size {
        let new_res = build_term!(
            pool,
            (or (and (= {x[i].clone()} {y[i].clone()}) {expected_res.clone()})
                (and (not {x[i].clone()}) {y[i].clone()}))
        );
        expected_res = new_res;
    }

    assert_eq(&expected_res, res)
}

pub fn slt(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvslt x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let mut expected_res = build_term!(pool, (and {x[0].clone()} (not {y[0].clone()})));

    for i in 1..(size - 1) {
        let new_res = build_term!(
            pool,
            (or (and (= {x[i].clone()} {y[i].clone()}) {expected_res.clone()})
                (and (not {x[i].clone()}) {y[i].clone()}))
        );
        expected_res = new_res;
    }

    let new_res = build_term!(
        pool,
        (or
         (and {x[size - 1].clone()} (not {y[size - 1].clone()}))
         (and (and {x[size - 1].clone()} {y[size - 1].clone()}) {expected_res.clone()}))
    );
    expected_res = new_res;

    assert_eq(&expected_res, res)
}

pub fn add(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (bvadd x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let mut carries = vec![pool.bool_false()];

    for i in 1..size {
        let carry_i = build_term!(
          pool,
          (or (and {x[i - 1].clone()} {y[i - 1].clone()}) (and (xor {x[i - 1].clone()} {y[i - 1].clone()}) {carries[i - 1].clone()}))
        );
        carries.push(carry_i);
    }

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
          pool,
          (xor (xor {x[i].clone()} {y[i].clone()}) {carries[i].clone()})
        )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}


pub fn neg(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (x, res) = match_term_err!((= (bvneg x) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };

    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);

    let mut carries = vec![pool.bool_true()];

    for i in 1..size {
        let carry_i = build_term!(
          pool,
          (or (and (not {x[i - 1].clone()}) false) (and (xor (not {x[i - 1].clone()}) false) {carries[i - 1].clone()}))
        );
        carries.push(carry_i);
    }

    let res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
          pool,
          (xor (xor (not {x[i].clone()}) false) {carries[i].clone()})
        )
        })
        .collect();

    let expected_res = pool.add(Term::Op(Operator::BvBbTerm, res_args));

    assert_eq(&expected_res, res)
}

//TODO I think this can be redone with build_term_vec.
pub fn extract(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let (((_, left_j), left_x), right) =
        match_term_err!((= ((_ extract i j) x) (bbterm ...)) = &conclusion[0])?;

    let left_j = left_j.as_integer().unwrap();
    let mut index = left_j;

    if let Some((Operator::BvBbTerm, args)) = left_x.as_op() {
        let mut index = index.to_usize().unwrap();
        for arg in right {
            assert_eq(&args[index], arg)?;
            index += 1;
        }
        return Ok(());
    }

    for arg in right {
        let expected_arg = Term::IndexedOp {
            op: IndexedOperator::BvBitOf,
            op_args: vec![Constant::Integer(index.clone())],
            args: vec![left_x.clone()],
        };
        let new_arg = pool.add(expected_arg);
        assert_eq(&new_arg, arg)?;
        index += 1;
    }
    Ok(())
}

pub fn concat(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res_vec) = match_term_err!((= (concat x y) (bbterm ...)) = &conclusion[0])?;

    let Sort::BitVec(size1) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };
    let size1 = size1.to_usize().unwrap();

    let Sort::BitVec(size2) = pool.sort(y).as_sort().cloned().unwrap() else {
        unreachable!();
    };
    let size2 = size2.to_usize().unwrap();

    let x = build_term_vec(x, size1, pool);
    let y = build_term_vec(y, size2, pool);

    let mut index = 0;
    for arg in res_vec {
        if index < size1 { assert_eq(&x[index], arg)?; }
        else { assert_eq(&y[index - size1], arg)?; }

        index += 1;
    }
    Ok(())
}

pub fn equality(RuleArgs { conclusion, pool, .. }: RuleArgs) -> RuleResult {
    assert_clause_len(conclusion, 1)?;
    let ((x, y), res) = match_term_err!((= (= x y) res) = &conclusion[0])?;

    let Sort::BitVec(size) = pool.sort(x).as_sort().cloned().unwrap() else {
        unreachable!();
    };
    let size = size.to_usize().unwrap();

    let x = build_term_vec(x, size, pool);
    let y = build_term_vec(y, size, pool);

    let expected_res_args: Vec<_> = (0..size)
        .map(|i| {
            build_term!(
                pool,
                (= {x[i].clone()} {y[i].clone()})
            )
        })
        .collect();
    let expected_res = pool.add(Term::Op(Operator::And, expected_res_args));

    assert_eq(&expected_res, res)
}

mod tests {
    #[test]
    fn ult() {
        test_cases! {
            definitions = "
                (declare-fun x4 () (_ BitVec 4))
                (declare-fun y4 () (_ BitVec 4))
            ",
            "Using bvult with x and y as bitvectors" {
              "(step t3 (cl (= (bvult x4 y4) (or (= ((_ bit_of 3) x4) ((_ bit_of 2) y4)) ((_ bit_of 3) x4) ((_ bit_of 2) y4)))) :rule bitblast_ult)": false,
              "(step t3 (cl (= (bvult x4 y4) (or (and (= ((_ bit_of 3) x4) ((_ bit_of 3) y4)) (or (and (= ((_ bit_of 2) x4) ((_ bit_of 2) y4)) (or (and (= ((_ bit_of 1) x4) ((_ bit_of 1) y4)) (and (not ((_ bit_of 0) x4)) ((_ bit_of 0) y4))) (and (not ((_ bit_of 1) x4)) ((_ bit_of 1) y4)))) (and (not ((_ bit_of 2) x4)) ((_ bit_of 2) y4)))) (and (not ((_ bit_of 3) x4)) ((_ bit_of 3) y4))))) :rule bitblast_ult)": true,
            }
            "Using bvult with x and y as bbterms" {
              "(step t1 (cl (= (bvult (bbterm ((_ bit_of 0) x4) ((_ bit_of 1) x4) ((_ bit_of 2) x4) ((_ bit_of 3) x4)) (bbterm ((_ bit_of 0) y4) ((_ bit_of 1) y4) ((_ bit_of 2) y4) ((_ bit_of 3) y4))) (or (and (= ((_ bit_of 3) x4) ((_ bit_of 3) y4)) (or (and (= ((_ bit_of 2) x4) ((_ bit_of 2) y4)) (or (and (= ((_ bit_of 1) x4) ((_ bit_of 1) y4)) (and (not ((_ bit_of 0) x4)) ((_ bit_of 0) y4))) (and (not ((_ bit_of 1) x4)) ((_ bit_of 1) y4)))) (and (not ((_ bit_of 2) x4)) ((_ bit_of 2) y4)))) (and (not ((_ bit_of 3) x4)) ((_ bit_of 3) y4))))) :rule bitblast_ult)": true,
              "(step t2 (cl (= (bvult (bbterm ((_ bit_of 0) x4) ((_ bit_of 1) x4) ((_ bit_of 2) x4) ((_ bit_of 3) x4)) (bbterm ((_ bit_of 4) y4) ((_ bit_of 1) y4) ((_ bit_of 2) y4) ((_ bit_of 3) y4))) (or (and (= ((_ bit_of 3) x4) ((_ bit_of 3) y4)) (or (and (= ((_ bit_of 2) x4) ((_ bit_of 2) y4)) (or (and (= ((_ bit_of 1) x4) ((_ bit_of 1) y4)) (and (not ((_ bit_of 0) x4)) ((_ bit_of 0) y4))) (and (not ((_ bit_of 1) x4)) ((_ bit_of 1) y4)))) (and (not ((_ bit_of 2) x4)) ((_ bit_of 2) y4)))) (and (not ((_ bit_of 3) x4)) ((_ bit_of 3) y4))))) :rule bitblast_ult)": false,
            }
        }
    }

    #[test]
    fn add() {
        test_cases! {
            definitions = "
                (declare-fun x4 () (_ BitVec 4))
                (declare-fun y4 () (_ BitVec 4))
            ",
            "Using bvadd with x and y as bitvectors" {
              "(step t3 (cl (= (bvadd x4 y4) (bbterm ((_ bit_of 0) x4) ((_ bit_of 1) y4) ((_ bit_of 2) x4) ((_ bit_of 3) y4)))) :rule bitblast_bvadd)": false,
              "(step t4 (cl (= (bvadd x4 y4) (bbterm (xor (xor ((_ bit_of 0) x4) ((_ bit_of 0) y4)) false) (xor (xor ((_ bit_of 1) x4) ((_ bit_of 1) y4)) (or (and ((_ bit_of 0) x4) ((_ bit_of 0) y4)) (and (xor ((_ bit_of 0) x4) ((_ bit_of 0) y4)) false))) (xor (xor ((_ bit_of 2) x4) ((_ bit_of 2) y4)) (or (and ((_ bit_of 1) x4) ((_ bit_of 1) y4)) (and (xor ((_ bit_of 1) x4) ((_ bit_of 1) y4)) (or (and ((_ bit_of 0) x4) ((_ bit_of 0) y4)) (and (xor ((_ bit_of 0) x4) ((_ bit_of 0) y4)) false))))) (xor (xor ((_ bit_of 3) x4) ((_ bit_of 3) y4)) (or (and ((_ bit_of 2) x4) ((_ bit_of 2) y4)) (and (xor ((_ bit_of 2) x4) ((_ bit_of 2) y4)) (or (and ((_ bit_of 1) x4) ((_ bit_of 1) y4)) (and (xor ((_ bit_of 1) x4) ((_ bit_of 1) y4)) (or (and ((_ bit_of 0) x4) ((_ bit_of 0) y4)) (and (xor ((_ bit_of 0) x4) ((_ bit_of 0) y4)) false)))))))))) :rule bitblast_bvadd)": true,
            }
            "Using bvadd with x and y as bbterms" {
              "(step t1 (cl (= (bvadd (bbterm false (xor (xor (not ((_ bit_of 0) x4)) false) true) (xor (xor (not ((_ bit_of 1) x4)) false) (or (and (not ((_ bit_of 0) x4)) false) (and (xor (not ((_ bit_of 0) x4)) false) true))) (xor (xor (not ((_ bit_of 2) x4)) false) (or (and (not ((_ bit_of 1) x4)) false) (and (xor (not ((_ bit_of 1) x4)) false) (or (and (not ((_ bit_of 0) x4)) false) (and (xor (not ((_ bit_of 0) x4)) false) true)))))) (bbterm true true true true)) (bbterm (xor (xor false true) false) (xor (xor (xor (xor (not ((_ bit_of 0) x4)) false) true) true) (or (and false true) (and (xor false true) false))) (xor (xor (xor (xor (not ((_ bit_of 1) x4)) false) (or (and (not ((_ bit_of 0) x4)) false) (and (xor (not ((_ bit_of 0) x4)) false) true))) true) (or (and (xor (xor (not ((_ bit_of 0) x4)) false) true) true) (and (xor (xor (xor (not ((_ bit_of 0) x4)) false) true) true) (or (and false true) (and (xor false true) false))))) (xor (xor (xor (xor (not ((_ bit_of 2) x4)) false) (or (and (not ((_ bit_of 1) x4)) false) (and (xor (not ((_ bit_of 1) x4)) false) (or (and (not ((_ bit_of 0) x4)) false) (and (xor (not ((_ bit_of 0) x4)) false) true))))) true) (or (and (xor (xor (not ((_ bit_of 1) x4)) false) (or (and (not ((_ bit_of 0) x4)) false) (and (xor (not ((_ bit_of 0) x4)) false) true))) true) (and (xor (xor (xor (not ((_ bit_of 1) x4)) false) (or (and (not ((_ bit_of 0) x4)) false) (and (xor (not ((_ bit_of 0) x4)) false) true))) true) (or (and (xor (xor (not ((_ bit_of 0) x4)) false) true) true) (and (xor (xor (xor (not ((_ bit_of 0) x4)) false) true) true) (or (and false true) (and (xor false true) false)))))))))) :rule bitblast_bvadd)": true,
              "(step t2 (cl (= (bvadd (bbterm false (xor (xor (not ((_ bit_of 0) x4)) false) true) (xor (xor (not ((_ bit_of 1) x4)) false) (or (and (not ((_ bit_of 0) x4)) false) (and (xor (not ((_ bit_of 0) x4)) false) true))) (xor (xor (not ((_ bit_of 2) x4)) false) (or (and (not ((_ bit_of 1) x4)) false) (and (xor (not ((_ bit_of 1) x4)) false) (or (and (not ((_ bit_of 0) x4)) false) (and (xor (not ((_ bit_of 0) x4)) false) true)))))) (bbterm true true true true)) (bbterm (xor (xor false true) false) (xor (xor (xor (xor (not ((_ bit_of 0) x4)) false) true) true) (or (and false true) (and (xor false true) false))) (xor (xor (xor (xor (not ((_ bit_of 1) x4)) false) (or (and (not ((_ bit_of 0) x4)) false) (and (xor (not ((_ bit_of 0) x4)) false) true))) true) (or (and (xor (xor (not ((_ bit_of 0) x4)) false) true) true) (and (xor (xor (xor (not ((_ bit_of 0) x4)) false) true) true) (or (and false true) (and (xor false true) false))))) (xor (xor (xor (xor (not ((_ bit_of 2) x4)) false) (or (and (not ((_ bit_of 1) x4)) false) (and (xor (not ((_ bit_of 1) x4)) false) (or (and (not ((_ bit_of 0) x4)) false) (and (xor (not ((_ bit_of 0) x4)) false) true))))) true) (or (and (xor (xor (not ((_ bit_of 1) x4)) false) (or (and (not ((_ bit_of 0) x4)) false) (and (xor (not ((_ bit_of 0) x4)) false) true))) true) (and (xor (xor (xor (not ((_ bit_of 1) x4)) false) (or (and (not ((_ bit_of 0) x4)) false) (and (xor (not ((_ bit_of 0) x4)) false) true))) true) (or (and (xor (xor (not ((_ bit_of 0) x4)) false) true) true) (and (xor (xor (xor (not ((_ bit_of 0) x4)) false) true) true) (or (and true true) (and (xor false true) false)))))))))) :rule bitblast_bvadd)": false,
            }
        }
    }
    #[test]
    fn extract() {
        test_cases! {
            definitions = "
                (declare-fun a () Bool)
                (declare-fun zz () (_ BitVec 12))
                (declare-fun xx () (_ BitVec 12))
            ",
            "Using extract with x and y as bbterms" {
              "(step t2 (cl (= ((_ extract 1 0) (bbterm ((_ bit_of 0) (ite a #b110 #b011)) ((_ bit_of 1) (ite a #b110 #b011)) ((_ bit_of 2) (ite a #b110 #b011)))) (bbterm ((_ bit_of 0) (ite a #b110 #b011)) ((_ bit_of 1) (ite a #b110 #b011))))) :rule bitblast_extract)": true,
              "(step t3 (cl (= ((_ extract 1 0) (bbterm ((_ bit_of 0) (ite a #b110 #b011)) ((_ bit_of 1) (ite a #b110 #b011)) ((_ bit_of 2) (ite a #b110 #b011)))) (bbterm ((_ bit_of 0) (ite a #b111 #b011)) ((_ bit_of 1) (ite a #b111 #b011))))) :rule bitblast_extract)": false,
              "(step t2 (cl (= ((_ extract 1 0) (bbterm ((_ bit_of 0) (ite a #b110 #b011)) ((_ bit_of 1) (ite a #b110 #b011)) ((_ bit_of 2) (ite a #b110 #b011)))) (bbterm ((_ bit_of 1) (ite a #b110 #b011)) ((_ bit_of 1) (ite a #b110 #b011))))) :rule bitblast_extract)": false,
              "(step t4 (cl (= ((_ extract 11 4) (bbterm ((_ bit_of 0) zz) ((_ bit_of 1) zz) ((_ bit_of 2) zz) ((_ bit_of 3) zz) ((_ bit_of 4) zz) ((_ bit_of 5) zz) ((_ bit_of 6) zz) ((_ bit_of 7) zz) ((_ bit_of 8) zz) ((_ bit_of 9) zz) ((_ bit_of 10) zz) ((_ bit_of 11) zz))) (bbterm ((_ bit_of 4) zz) ((_ bit_of 5) zz) ((_ bit_of 6) zz) ((_ bit_of 7) zz) ((_ bit_of 8) zz) ((_ bit_of 9) zz) ((_ bit_of 10) zz) ((_ bit_of 11) zz)))) :rule bitblast_extract)": true,
              "(step t5 (cl (= ((_ extract 11 4) (bbterm ((_ bit_of 0) zz) ((_ bit_of 1) zz) ((_ bit_of 2) zz) ((_ bit_of 3) zz) ((_ bit_of 4) zz) ((_ bit_of 5) zz) ((_ bit_of 6) zz) ((_ bit_of 7) zz) ((_ bit_of 8) zz) ((_ bit_of 9) zz) ((_ bit_of 10) zz) ((_ bit_of 11) zz))) (bbterm ((_ bit_of 3) zz) ((_ bit_of 5) zz) ((_ bit_of 6) zz) ((_ bit_of 7) zz) ((_ bit_of 8) zz) ((_ bit_of 9) zz) ((_ bit_of 10) zz) ((_ bit_of 11) zz)))) :rule bitblast_extract)": false,
              "(step t5 (cl (= ((_ extract 11 4) (bbterm ((_ bit_of 0) zz) ((_ bit_of 1) zz) ((_ bit_of 2) zz) ((_ bit_of 3) zz) ((_ bit_of 4) zz) ((_ bit_of 5) zz) ((_ bit_of 6) zz) ((_ bit_of 7) zz) ((_ bit_of 8) zz) ((_ bit_of 9) zz) ((_ bit_of 10) zz) ((_ bit_of 11) zz))) (bbterm ((_ bit_of 4) xx) ((_ bit_of 5) zz) ((_ bit_of 6) zz) ((_ bit_of 7) zz) ((_ bit_of 8) zz) ((_ bit_of 9) zz) ((_ bit_of 10) zz) ((_ bit_of 11) zz)))) :rule bitblast_extract)": false,
            }
        }
    }
}
