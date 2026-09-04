/-
# LeanFormalizations

Root import. Each entry is a solved-but-unformalized result; the load-bearing
statements live in per-result `Statement.lean` audit surfaces.
-/
import LeanFormalizations.NumericalSemigroups.Curtis.Statement
import LeanFormalizations.NumericalSemigroups.Curtis.Anchors
import LeanFormalizations.NumericalSemigroups.Curtis.Boundary
import LeanFormalizations.RealAnalysis.PowerTower.Statement
import LeanFormalizations.NumberTheory.Transcendence.HermiteLindemann
import LeanFormalizations.NumberTheory.Transcendence.ETranscendental
import LeanFormalizations.NumberTheory.Transcendence.PiLindemann
import LeanFormalizations.NumberTheory.Transcendence.MonicRootSums
import LeanFormalizations.NumberTheory.Transcendence.SubsetSumEsymm
import LeanFormalizations.NumberTheory.Transcendence.PiTranscendental
import LeanFormalizations.Geometry.Constructible.Statement
import LeanFormalizations.Logic.Goodstein.Statement
import LeanFormalizations.Logic.Goodstein.Anchors
import LeanFormalizations.Logic.Goodstein.Length
import LeanFormalizations.Logic.Goodstein.Growth
import LeanFormalizations.Logic.Goodstein.Domination
import LeanFormalizations.Logic.Goodstein.GoodsteinLike
import LeanFormalizations.Logic.Goodstein.DominationBaseCases
import LeanFormalizations.Logic.Goodstein.DominationCorollary
import LeanFormalizations.Logic.Goodstein.DominationOmega
import LeanFormalizations.Logic.Goodstein.TowerDomination
import LeanFormalizations.Logic.Goodstein.GrowthStatement
import LeanFormalizations.Logic.FastGrowing.Basic
import LeanFormalizations.Logic.FastGrowing.Hardy
import LeanFormalizations.Logic.FastGrowing.Domination
-- No-three-in-line (Green's problem #72): two independent constructions of the
-- 3(p−1) lower bound share one core. The `hyperbolaWide`/arc development:
import LeanFormalizations.Combinatorics.NoThreeInLine.Statement
import LeanFormalizations.Combinatorics.NoThreeInLine.Hyperbola
import LeanFormalizations.Combinatorics.NoThreeInLine.HyperbolaLine
import LeanFormalizations.Combinatorics.NoThreeInLine.Pinwheel
import LeanFormalizations.Combinatorics.NoThreeInLine.Anchors
-- The sheared-hyperbola (HJSW) development + its prime-gap consequence:
import LeanFormalizations.Combinatorics.NoThreeInLine.Shear.Hyperbola
import LeanFormalizations.Combinatorics.NoThreeInLine.Shear.Anchors
import LeanFormalizations.Combinatorics.NoThreeInLine.Shear.Statement
import LeanFormalizations.Combinatorics.NoThreeInLine.Shear.PrimeGap
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Statement
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.FaithfulnessCheck
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.SmallCases
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Tube
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.TubeFractional
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Discretize
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Directions
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Cordoba
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.CordobaL2
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Frostman
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Cover
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.NetThinning
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.MeasurableRoute
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Wiring
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.Selection
import LeanFormalizations.GeometricMeasureTheory.Kakeya2D.DeepMindBridge
import LeanFormalizations.NumberTheory.PrimeNumberTheorem.PNT
import LeanFormalizations.NumberTheory.PrimeNumberTheorem.Mertens
import LeanFormalizations.NumberTheory.PrimeNumberTheorem.MertensConstant
import LeanFormalizations.NumberTheory.DivisorProblem
import LeanFormalizations.RealAnalysis.BVFourierDecay
-- Catalan's constant: the salvage of Sun's arXiv:2609.04176v1 (Thm 2.1) + the 2-adic no-go.
import LeanFormalizations.NumberTheory.Catalan.Tails
import LeanFormalizations.NumberTheory.Catalan.Residual
import LeanFormalizations.NumberTheory.Catalan.TwoAdic
import LeanFormalizations.NumberTheory.Catalan.Statement
import LeanFormalizations.NumberTheory.Catalan.Frame

-- Dirichlet beta values: Phase 4 — one of β(2), β(4), …, β(20) is irrational
-- (Rivoal–Zudilin 2003 / Zudilin 2019 §2, elementary route).  β(2) = Catalan's constant.
import LeanFormalizations.NumberTheory.DirichletBeta.Beta
import LeanFormalizations.NumberTheory.DirichletBeta.Rational
import LeanFormalizations.NumberTheory.DirichletBeta.CompleteMonotone
import LeanFormalizations.NumberTheory.DirichletBeta.PartialFractions
import LeanFormalizations.NumberTheory.DirichletBeta.LinearForm
import LeanFormalizations.NumberTheory.DirichletBeta.Integral
import LeanFormalizations.NumberTheory.DirichletBeta.Bound
import LeanFormalizations.NumberTheory.DirichletBeta.Lcm
import LeanFormalizations.NumberTheory.DirichletBeta.Statement
