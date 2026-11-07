module

public import Chapter03OAExecModel
public import Chapter03OAExecArticleOtherData

@[expose] public section

noncomputable section
open Chapter02 Chapter02DICOPTExamples Chapter03.OAKKT
namespace Chapter03.OAExec.Article

def Gdata : Data 1 1 1 2 where
  model := G
  f := Gf
  Df := Gdf
  Dg := Gdg
  domain := Set.univ

def Tdata : Data 1 1 1 2 where
  model := T
  f := Tf
  Df := Tdf
  Dg := Tdg
  domain := Set.univ

def Adata : Data 1 1 1 2 where
  model := A
  f := Af
  Df := Adf
  Dg := Adg
  domain := Set.univ

theorem G_analytic : Analytic Gdata where
  convex_f := quadratic_convex _
  convex_g _ := xSquareRow_convex _
  original_domain _ _ := Set.mem_univ _
  derivative_f _ _ := quadratic_derivative _ _
  derivative_g _ _ _ := xSquareRow_derivative _ _

theorem T_analytic : Analytic Tdata where
  convex_f := linearQuadratic_convex _
  convex_g _ := xSquareRow_convex _
  original_domain _ _ := Set.mem_univ _
  derivative_f _ _ := linearQuadratic_derivative _ _
  derivative_g _ _ _ := xSquareRow_derivative _ _

theorem A_analytic : Analytic Adata where
  convex_f := quadratic_convex _
  convex_g _ := by
    simpa [Adata,A,boxModel,Pi.add_def,sub_eq_add_neg] using
      (quadratic_convex (1/2)).add_const (-(1/16))
  original_domain _ _ := Set.mem_univ _
  derivative_f _ _ := quadratic_derivative _ _
  derivative_g _ _ _ := (quadratic_derivative _ _).sub_const _

def G_event (y : IntVector 1) (hy : y ∈ IntegerBox G.lo G.hi) : Event Gdata where
  target := y
  target_mem := hy
  x := scalar 0
  restoration := none

theorem G_event_valid (y : IntVector 1) (hy : y ∈ IntegerBox G.lo G.hi) :
    EventValid Gdata (G_event y hy) :=
  ⟨Set.mem_univ _,G_fiber_minimum _,⟨G_fixed _⟩⟩

theorem G_event_characterization (e : Event Gdata) (he : EventValid Gdata e) :
    e.restoration=none ∧ e.x=scalar 0 := by
  have hn : e.restoration=none := by
    by_contra h
    exact event_empty he h ⟨scalar 0,(G_fiber_minimum (intCast e.target)).1⟩
  refine ⟨hn,?_⟩
  have hm := he.2
  rw [hn] at hm
  exact G_fiber_minimum_unique (intCast e.target) e.x hm.1

def T_event (y : IntVector 1) (hy : y ∈ IntegerBox T.lo T.hi) : Event Tdata where
  target := y
  target_mem := hy
  x := scalar 0
  restoration := none

theorem T_event_valid (y : IntVector 1) (hy : y ∈ IntegerBox T.lo T.hi) :
    EventValid Tdata (T_event y hy) :=
  ⟨Set.mem_univ _,T_fiber_minimum _,⟨T_fixed _⟩⟩

def A_event (y : IntVector 1) (hy : y ∈ IntegerBox A.lo A.hi) : Event Adata where
  target := y
  target_mem := hy
  x := scalar 0
  restoration := some (scalar (3/16))

theorem A_event_valid (y : IntVector 1) (hy : y ∈ IntegerBox A.lo A.hi) :
    EventValid Adata (A_event y hy) :=
  ⟨Set.mem_univ _,A_fiber_empty y hy,A_restoration_minimum y hy⟩

def EmptyData : Data 1 1 1 2 where
  model := EmptyInitial
  f := Gf
  Df := Gdf
  Dg := Gdg
  domain := Set.univ

def IntegralData : Data 1 1 1 2 where
  model := G
  f := IntegralF
  Df := quadraticD 0
  Dg := Gdg
  domain := Set.univ

end Chapter03.OAExec.Article
