#![rr::import("rrstd.iterator.theories", "map")]

/// We pick an invariant Inv
/// TODO: maybe release Inv when we drop the Map iterator
#[rr::only_spec]
#[rr::params("Inv" : "thread_id → {xt_of I} → {xt_of F} → iProp Σ")]
/// Precondition: The picked invariant should hold initially.
#[rr::requires(#iris "Inv π it f")]
/// Precondition: persistently, each iteration preserves the invariant.
/// If the inner iterator has been advanced, we can call the closure.
#[rr::requires(#iris "□ (∀ it_state it_state' clos_state e,
    {I::Next} π it_state (Some e) it_state' -∗
    Inv π it_state clos_state -∗
    {F::Pre} π clos_state *[e] ∗
    (∀ e' clos_state', {F::PostMut} π clos_state *[e] clos_state' e' -∗ Inv π it_state' clos_state'))")]
/// Precondition: If no element is emitted, the invariant is also upheld.
#[rr::requires(#iris "□ (∀ it_state it_state' clos_state,
    {I::Next} π it_state None it_state' -∗
    Inv π it_state clos_state -∗
    Inv π it_state' clos_state)")]
#[rr::returns("mk_map_x it f")]
pub fn map<B, I, F>(it: I, f: F) -> RRMap<B, I, F>
where
    I: Sized,
    I: Iterator,
    F: FnMut(I::Item) -> B,
{
    RRMap::<B, I, F>::new(it, f)
}

// TODO: problematic for this specification: The trait bounds for I, F are not in scope here.
// TODO: should we expose the closure state?
#[rr::refined_by("x" : "MapXRT {rt_of I} {rt_of F}")]
#[rr::exists("Inv" : "thread_id → {xt_of I} → {xt_of F} → iProp Σ")]
/// The map invariant holds.
#[rr::invariant(#own "Inv π x.(map_it) x.(map_clos)")]
/// Given the invariant, we can advance the iterator:
#[rr::invariant(#own "li_sealed (□ (∀ it_state it_state' clos_state e,
    {I::Next} π it_state (Some e) it_state' -∗
    Inv π it_state clos_state -∗
    {F::Pre} π clos_state *[e] ∗
    (∀ e' clos_state', {F::PostMut} π clos_state *[e] clos_state' e' -∗ Inv π it_state' clos_state')))")]
/// If no element is emitted, the invariant is also upheld.
#[rr::invariant(#own "li_sealed (□ (∀ it_state it_state' clos_state,
    {I::Next} π it_state None it_state' -∗
    Inv π it_state clos_state -∗
    Inv π it_state' clos_state))")]
pub struct RRMap<B, I, F>
where
    I: Iterator,
    F: FnMut(I::Item) -> B,
{
    #[rr::field("$# x.(map_it)")]
    pub(crate) iter: I,
    #[rr::field("$# x.(map_clos)")]
    f: F,
}

impl<B, I, F> RRMap<B, I, F>
where
    I: Iterator,
    F: FnMut(I::Item) -> B,
{
    #[rr::only_spec]
    #[rr::params("Inv" : "thread_id → {xt_of I} → {xt_of F} → iProp Σ")]
    /// Precondition: The picked invariant should hold initially.
    #[rr::requires(#iris "Inv π iter f")]
    /// Precondition: persistently, each iteration preserves the invariant.
    /// If the inner iterator has been advanced, we can call the closure.
    #[rr::requires(#iris "li_sealed (□ (∀ it_state it_state' clos_state e,
        {I::Next} π it_state (Some e) it_state' -∗
        Inv π it_state clos_state -∗
        {F::Pre} π clos_state *[e] ∗
        (∀ e' clos_state', {F::PostMut} π clos_state *[e] clos_state' e' -∗ Inv π it_state' clos_state')))")]
    /// Precondition: If no element is emitted, the invariant is also upheld.
    #[rr::requires(#iris "li_sealed (□ (∀ it_state it_state' clos_state,
        {I::Next} π it_state None it_state' -∗
        Inv π it_state clos_state -∗
        Inv π it_state' clos_state))")]
    #[rr::returns("mk_map_x iter f")]
    pub(crate) fn new(iter: I, f: F) -> RRMap<B, I, F> {
        RRMap { iter, f }
    }

    pub(crate) fn into_inner(self) -> I {
        self.iter
    }
}

/// Spec: We have the pure parts of the inner Next and the pre- and postconditions.
#[rr::instantiate("Next" := "(λ π s1 e s2,
        if_iNone e ({MI::Next} π s1.(map_it) None s2.(map_it)) ∗
        if_iSome e (λ e, ∃ e_inner,
            boringly ({MI::Next} π s1.(map_it) (Some e_inner) s2.(map_it)) ∗
            boringly ({MF::Pre} π s1.(map_clos) *[e_inner]) ∗
            boringly ({MF::PostMut} π s1.(map_clos) *[e_inner] s2.(map_clos) e)
            ))%I")]
impl<MB, MI: Iterator, MF> Iterator for RRMap<MB, MI, MF>
where MF: FnMut(MI::Item) -> MB
{
    type Item = MB;

    #[rr::only_spec]
    #[rr::default_spec]
    fn next(&mut self) -> Option<MB> {
        self.iter
            // Calling next is possible without preconditions.
            .next()
            // Calling the closure requires us to prove its precondition.
            .map(&mut self.f)
    }
}
