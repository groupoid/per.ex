type Name = String;

#[derive(Debug, Clone)]
pub enum Pattern {
    Pair(Box<Pattern>, Box<Pattern>),
    Unit,
    Var(Name),
}


type Level = u32;
#[derive(Debug, Clone)]
pub enum Per {
    Lambda(Box<Pattern>, Box<Per>),
    Type(Level),
    Pi(Box<Pattern>, Box<Per>, Box<Per>),
    Sigma(Box<Pattern>, Box<Per>, Box<Per>),
    Pair(Box<Per>, Box<Per>),
    First(Box<Per>),
    Second(Box<Per>),
    Application(Box<Per>, Box<Per>),
    Var(Name),
    Declaration(Box<Decl>, Box<Per>),
}

pub type Decl = (Pattern, Per, Per);

#[derive(Debug, Clone)]
pub enum Value {
    VLam(Clos),
    VPair(Box<Value>, Box<Value>),
    VSet(Level),
    VPi(Box<Value>, Clos),
    VSig(Box<Value>, Clos),
    VNt(Neut),
}

#[derive(Debug, Clone)]
pub enum Neut {
    NGen(i32),
    NApp(Box<Neut>, Box<Value>),
    NFst(Box<Neut>),
    NSnd(Box<Neut>),
}


#[derive(Debug, Clone)]
pub struct  Clos(Pattern, Per, Rho);

#[derive(Debug, Clone)]
pub enum Rho {
    Nil,
    UpVar(Box<Rho>, Pattern, Box<Value>),
    UpDec(Box<Rho>, Decl),
}


#[derive(Debug, Clone, PartialEq)]
pub enum NExp {
    NELam(i32, Box<NExp>),
    NEPair(Box<NExp>, Box<NExp>),
    NESet(Level),
    NEPi(Box<NExp>, i32, Box<NExp>),
    NESig(Box<NExp>, i32, Box<NExp>),
    NENt(NNeut),
}

#[derive(Debug, Clone, PartialEq)]
pub enum NNeut {
    NtGen(i32),
    NtApp(Box<NNeut>, Box<NExp>),
    NtFst(Box<NNeut>),
    NtSnd(Box<NNeut>),
}

#[derive(Debug, Clone)]
pub enum NRho {
    Nil,
    UpVar(Box<NRho>, Pattern, Box<NExp>),
    UpDec(Box<NRho>, Decl),
}


#[derive(Debug, Clone)]
pub struct CoreError(String);

fn vfst(value: Value) -> Result<Value, CoreError> {
    match value {
        Value::VPair(u, _) => Ok(*u),
        Value::VNt(k) => Ok(Value::VNt(Neut::NFst(Box::new(k)))),
        _ => Err(CoreError("vfst".to_string())),
    }
}

fn vsnd(value: Value) -> Result<Value, CoreError> {
    match value {
        Value::VPair(_, u) => Ok(*u),
        Value::VNt(k) => Ok(Value::VNt(Neut::NSnd(Box::new(k)))),
        _ => Err(CoreError("vsnd".to_string())),
    }
}

fn in_pat(x: &str, patt: &Pattern) -> bool {
    match patt {
        Pattern::Unit => false,
        Pattern::Var(y) => x == y,
        Pattern::Pair(p1, p2) => in_pat(x, p1) || in_pat(x, p2),
    }
}

fn pat_proj(p: &Pattern, x: &str, v: Value) -> Result<Value, CoreError> {
    match p {
        Pattern::Var(y) if x == y => Ok(v.clone()),
        Pattern::Pair(p1, p2) => {
           if in_pat(x, p1) { pat_proj(p1, x, vfst(v.clone())?) }
            else if in_pat(x, p2) { pat_proj(p2, x, vsnd(v.clone())?) }
            else { Err(CoreError("patProj".to_string())) }
       }
        _ => Err(CoreError("patProj".to_string())),
    }
}

fn l_rho(rho: &Rho) -> i32 {
    match rho {
        Rho::Nil => 0,
        Rho::UpVar(r, _, _) => l_rho(r) + 1,
        Rho::UpDec(r, _) => l_rho(r) + 1,
    }
}

fn eval(e: &Per, rho: &Rho) -> Result<Value, CoreError> {
    match e {
        Per::Type(level) => Ok(Value::VSet(*level)),
        Per::Declaration(d, e) => eval(e, &Rho::UpDec(Box::new(rho.clone()), (**d).clone())),
        Per::Lambda(p, e) => Ok(Value::VLam(Clos(*(*p).clone(), (**e).clone(), rho.clone()))),
        Per::Pi(p, a, b) => Ok(Value::VPi(Box::new(eval(a, rho)?), Clos(*p.clone(), (**b).clone(), rho.clone()))),
        Per::Sigma(p, a, b) => Ok(Value::VSig(Box::new(eval(a, rho)?), Clos(*p.clone(), (**b).clone(), rho.clone()))),
        Per::First(e) => vfst(eval(e, rho)?),
        Per::Second(e) => vsnd(eval(e, rho)?),
        Per::Application(f, x) => app(eval(f, rho)?, eval(x, rho)?),
        Per::Var(x) => get_rho(rho, x),
        Per::Pair(e1, e2) => Ok(Value::VPair(Box::new(eval(e1, rho)?), Box::new(eval(e2, rho)?))),
    }
}

fn app(v1: Value, v2: Value) -> Result<Value, CoreError> {
    match (v1, v2) {
        (Value::VLam(f), v) => clos_by_val(f, v),
        (Value::VNt(k), m) => Ok(Value::VNt(Neut::NApp(Box::new(k), Box::new(m)))),
        _ => Err(CoreError("app".to_string())),
    }
}

fn clos_by_val(x: Clos, v: Value) -> Result<Value, CoreError> {
    eval(&x.1, &Rho::UpVar(Box::new(x.2),x.0, Box::new(v)))
}

fn get_rho(rho0: &Rho, x: &str) -> Result<Value, CoreError> {
    match rho0 {
        Rho::UpVar(rho, p, v) => {
            if in_pat(x, p) {
                pat_proj(p, x, *v.clone())
            } else {
                get_rho(rho, x)
            }
        }
        Rho::UpDec(rho, (p, _, e)) => {
            if in_pat(x, p) {
                pat_proj(p, x, eval(e, rho0)?)
            } else {
                get_rho(rho, x)
            }
        }
        _ => Err(CoreError("getRho".to_string())),
    }
}

type Gamma = std::collections::HashMap<String, Value>;

fn lookup(s: &str, lst: &Gamma) -> Result<Value, CoreError> {
    lst.get(s).cloned().ok_or_else(|| CoreError(format!("lookup {}", s)))
}

fn show_exp(e: &Per) -> String{
    format!("{:?}", e)
}

fn show_patt(p: &Pattern) -> String{
    format!("{:?}", p)
}

fn update(gma: &mut Gamma, p: &Pattern, v1: &Value, v2: &Value) -> Result<(), CoreError> {
    match (p, v1, v2) {
        (Pattern::Unit, _, _) => Ok(()),
        (Pattern::Var(x), t, _) => {
            gma.insert(x.clone(), t.clone());
            Ok(())
        }
        (Pattern::Pair(p1, p2), Value::VSig(t, g), v) => {
            update(gma, p1, t, &vfst(v.clone())?)?;
            update(gma, p2, &clos_by_val(g.clone(), vfst(v.clone())?)?, &vsnd(v.clone())?)
        }
        (p, _, _) => Err(CoreError(format!("update: p = {}", show_patt(p)))),
    }
}

fn gen_v(k: i32) -> Value {
    Value::VNt(Neut::NGen(k))
}

fn rb_v(k: i32, value: &Value) -> Result<NExp, CoreError> {
    match value {
        Value::VLam(f) => Ok(NExp::NELam(k, Box::new(rb_v(k + 1, &clos_by_val(f.clone(), gen_v(k))?)?))),
        Value::VPair(u, v) => Ok(NExp::NEPair(Box::new(rb_v(k, u)?), Box::new(rb_v(k, v)?))),
        Value::VSet(level) => Ok(NExp::NESet(*level)),
        Value::VPi(t, g) => Ok(NExp::NEPi(Box::new(rb_v(k, t)?), k, Box::new(rb_v(k + 1, &clos_by_val(g.clone(), gen_v(k))?)?))),
        Value::VSig(t, g) => Ok(NExp::NESig(Box::new(rb_v(k, t)?), k, Box::new(rb_v(k + 1, &clos_by_val(g.clone(), gen_v(k))?)?))),
        Value::VNt(l) => Ok(NExp::NENt(rb_n(k, l)?)),
    }
}

fn rb_n(i: i32, neut: &Neut) -> Result<NNeut, CoreError> {
    match neut {
        Neut::NGen(j) => Ok(NNeut::NtGen(*j)),
        Neut::NApp(k, m) => Ok(NNeut::NtApp(Box::new(rb_n(i, k)?), Box::new(rb_v(i, m)?))),
        Neut::NFst(k) => Ok(NNeut::NtFst(Box::new(rb_n(i, k)?))),
        Neut::NSnd(k) => Ok(NNeut::NtSnd(Box::new(rb_n(i, k)?))),
    }
}

fn rb_rho(i: i32, rho: &Rho) -> NRho {
    match rho {
        Rho::Nil => NRho::Nil,
        Rho::UpVar(rho, p, v) => NRho::UpVar(Box::new(rb_rho(i, rho)), p.clone(), Box::new(rb_v(i, v).unwrap())),
        Rho::UpDec(rho, d) => NRho::UpDec(Box::new(rb_rho(i, rho)), d.clone()),
    }
}

fn eq_nf(i: i32, m1: &Value, m2: &Value) -> Result<(), CoreError> {
    let e1 = rb_v(i, m1)?;
    let e2 = rb_v(i, m2)?;
    if e1 == e2 {
        Ok(())
    } else {
        dbg!(e1);
        dbg!(e2);
        Err(CoreError("eqNf".to_string()))
    }
}

fn show_val(u: &Value) -> String {
    format!("{:?}", u)
}

fn ext_pi_g(value: &Value) -> Result<(&Value, &Clos), CoreError> {
    if let Value::VPi(t, g) = value {
        Ok((t, g))
    } else {
        Err(CoreError(format!("extPiG {}", show_val(value))))
    }
}

fn ext_sig_g(value: &Value) -> Result<(&Value, &Clos), CoreError> {
    if let Value::VSig(t, g) = value {
        Ok((t, g))
    } else {
        Err(CoreError(format!("extSigG {}", show_val(value))))
    }
}

fn check_t(k: i32, rho: &Rho, gma: &mut Gamma, e: &Per) -> Result<(), CoreError> {
    match e {
        Per::Pi(p, a, b) => {
            check_t(k, rho, gma, a)?;
            let gen = gen_v(k);
            update(gma, p, &eval(a, rho)?, &gen)?;
            check_t(k + 1, &Rho::UpVar(Box::new(rho.clone()), *(*p).clone(), Box::new(gen)), gma, b)
        }
        Per::Sigma(p, a, b) => check_t(k, rho, gma, &Per::Pi(p.clone(), a.clone(), b.clone())),
        a => check(k, rho, gma, a, &Value::VSet(0)),
    }
}

fn check(k: i32, rho: &Rho, gma: &mut Gamma, e0: &Per, t0: &Value) -> Result<(), CoreError> {
    match (e0, t0) {
        (Per::Lambda(p, e), Value::VPi(t, g)) => {
            let gen = gen_v(k);
            update(gma, p, t, &gen)?;
            check(k + 1, &Rho::UpVar(Box::new(rho.clone()), *(*p).clone(), Box::new(gen.clone())), gma, e, &clos_by_val(g.clone(), gen)?)
        }
        (Per::Pair(e1, e2), Value::VSig(t, g)) => {
            check(k, rho, gma, e1, t)?;
            check(k, rho, gma, e2, &clos_by_val(g.clone(), eval(e1, rho)?)?)
        }
        (Per::Type(level), Value::VSet(_)) => Ok(()),
        (Per::Pi(p, a, b), Value::VSet(_)) => {
            check(k, rho, gma, a, &Value::VSet(0))?;
            let gen = gen_v(k);
            update(gma, p, &eval(a, rho)?, &gen)?;
            check(k + 1, &Rho::UpVar(Box::new(rho.clone()), *p.clone(), Box::new(gen.clone())), gma, b, &Value::VSet(0))
        }
        (Per::Sigma(p, a, b), Value::VSet(_)) => check(k, rho, gma, &Per::Pi(p.clone(), a.clone(), b.clone()), &Value::VSet(0)),
        (Per::Declaration(d, e), t) => {
            let gma1 = check_d(k, rho, gma, d)?;
            check(k, &Rho::UpDec(Box::new(rho.clone()), *d.clone()), &mut gma1.clone(), e, t)
        }
        (e, t) => eq_nf(k, t, &check_i(k, rho, gma, e)?),
    }
}

fn check_i(k: i32, rho: &Rho, gma: &mut Gamma, e: &Per) -> Result<Value, CoreError> {
    match e {
        Per::Type(level) => Ok(Value::VSet(*level)),
        Per::Var(x) => lookup(x, gma),
        Per::Application(f, x) => {
            let t1 = check_i(k, rho, gma, f)?;
            let (t, g) = ext_pi_g(&t1)?;
            check(k, rho, gma, x, t)?;
            clos_by_val(g.clone(), eval(x, rho)?)
        }
        Per::First(e) => {
            let t = check_i(k, rho, gma, e)?;
            Ok(ext_sig_g(&t)?.0.clone())
        }
        Per::Second(e) => {
            let t = check_i(k, rho, gma, e)?;
            let (_, g) = ext_sig_g(&t)?;
            clos_by_val(g.clone(), eval(e, rho)?)
        }
        e => Err(CoreError(format!("checkI: {}", show_exp(e)))),
    }
}

fn check_d(k: i32, rho: &Rho, gma: &mut Gamma, d: &Decl) -> Result<Gamma, CoreError> {
    let (p, a, e) = d;
    check_t(k, rho, gma, a)?;
    let t = eval(a, rho)?;
    let gen = gen_v(k);
    update(gma, p, &t, &gen)?;
    check(k + 1, &Rho::UpVar(Box::new(rho.clone()), p.clone(), Box::new(gen.clone())), gma, e, &t)?;
    let v = eval(e, &Rho::UpDec(Box::new(rho.clone()), d.clone()))?;
    update(gma, p, &t, &v)?;
    Ok(gma.clone())
}

pub fn check_main(e: &Per) -> Result<(), CoreError> {
    check(0, &Rho::Nil, &mut Gamma::new(), e, &Value::VSet(0))
}

