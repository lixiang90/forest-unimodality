import ForestUnimodality.FiniteKernelSequentialResidual
import ForestUnimodality.Stage130KernelData.Cell225.Parameters
import ForestUnimodality.BinomialMassData.Q653_1128.Batch000_049
import ForestUnimodality.BinomialMassData.Q653_1128.Batch050_099
import ForestUnimodality.BinomialMassData.Q653_1128.Batch100_149
import ForestUnimodality.BinomialMassData.Q653_1128.Batch150_199
import ForestUnimodality.BinomialMassData.Q7_12.Batch000_049
import ForestUnimodality.BinomialMassData.Q7_12.Batch050_099
import ForestUnimodality.BinomialMassData.Q7_12.Batch100_149
import ForestUnimodality.BinomialMassData.Q7_12.Batch150_199

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel000
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 0 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree000.table
  base := (392191631063931658096421983/20000000000000000000000000)
  polynomial :=
    { denominator := 240000000000000000000000000000000000000000
      center := (653)
      previous := (0)
      next := (475)
      square := (9467740176452132949691531440000000000000)
      linear := (-34235087055395658772738442400000000000000)
      constant := (4706299572767179897157063796000000000000000) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 0 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree000.table
  base := (392191631063931658096421983/20000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-17117543527697829386369221200000000000000)
      constant := (2353149786383589948578531898000000000000000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 0 interval.damping) (curvature.centralUpper 0 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree000.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 0 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 0 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel000

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel001
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (0/1)
  directionHi := (0/1)

def endpointA : IntegerEndpointWitness 1 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree001.table
  base := (26519808342399001996166264474510542002257/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-299519525354980133776683355641060000000000000)
      constant := (17024055257845174281488777863393646987499885344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 1 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree001.table
  base := (2107888794929432306749247225316251161599/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-67921175891884720821067843620000000000000)
      constant := (3828988024428180129767862861841752090878200) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 1 interval.damping) (curvature.centralUpper 1 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree001.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 1 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 1 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel001

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel002
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (0/1)
  centralHi := (0/1)
  directionLo := (49300664859163467021/100000000000000000000)
  directionHi := (24650332429581733511/50000000000000000000)

def endpointA : IntegerEndpointWitness 2 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree002.table
  base := (62480207327982123235917078263122173021273/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-372163128793853236866429053497320000000000000)
      constant := (10284136146407287309752689518971800374687428104) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 2 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree002.table
  base := (30912028461076246700606569833467630820373/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-84489721200675953483028023640000000000000)
      constant := (2304907421071355270068252178899669419066856) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 2 interval.damping) (curvature.centralUpper 2 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree002.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 2 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 2 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel002

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel003
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49300664859163467021/100000000000000000000)
  centralHi := (24650332429581733511/50000000000000000000)
  directionLo := (34860834438919814499/50000000000000000000)
  directionHi := (69721668877839628999/100000000000000000000)

def endpointA : IntegerEndpointWitness 3 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree003.table
  base := (40263836385940628839957873446792751387247/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-148268910744242113318724917117860000000000000)
      constant := (2329046332265746548361986939208073257546286952) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 3 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree003.table
  base := (9942497207155464573516753593316866326559/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-33686088836489062048329401220000000000000)
      constant := (521693044262125829534165467096709583674832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 3 interval.damping) (curvature.centralUpper 3 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree003.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 3 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 3 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel003

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel004
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34860834438919814499/50000000000000000000)
  centralHi := (69721668877839628999/100000000000000000000)
  directionLo := (85391256382996653193/100000000000000000000)
  directionHi := (42695628191498326597/50000000000000000000)

def endpointA : IntegerEndpointWitness 4 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree004.table
  base := (701891178561710402141039360197259039881/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-517450335671599443045920449209840000000000000)
      constant := (5327157523532288853198263580091926230999731520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 4 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree004.table
  base := (866321807874148635151741532519231749983/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-117626811818258418806948383680000000000000)
      constant := (1195145405472596452488538300622154975980416) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 4 interval.damping) (curvature.centralUpper 4 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree004.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 4 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 4 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel004

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel005
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (85391256382996653193/100000000000000000000)
  centralHi := (42695628191498326597/50000000000000000000)
  directionLo := (49300664859163467021/50000000000000000000)
  directionHi := (98601329718326934043/100000000000000000000)

def endpointA : IntegerEndpointWitness 5 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree005.table
  base := (20734109916516792781310938425217826255009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-590093939110472546135666147066100000000000000)
      constant := (4480079793901002538390896666053951080206671432) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 5 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree005.table
  base := (20475948790664790820849734121881547204977/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-134195357127049651468908563700000000000000)
      constant := (1007724971874557881508114093200235699379172) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 5 interval.damping) (curvature.centralUpper 5 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree005.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 5 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 5 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel005

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel006
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (49300664859163467021/50000000000000000000)
  centralHi := (98601329718326934043/100000000000000000000)
  directionLo := (110239637961024607937/100000000000000000000)
  directionHi := (55119818980512303969/50000000000000000000)

def endpointA : IntegerEndpointWitness 6 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree006.table
  base := (15853768257401164684603341984390653638781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-220912514183115216408470614974120000000000000)
      constant := (1355501243444965785201523176931489893313613496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 6 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree006.table
  base := (7827610849552736884044136868824406892537/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-50254634145280294710289581240000000000000)
      constant := (305763971316977402386212189121785765420888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 6 interval.damping) (curvature.centralUpper 6 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree006.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 6 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 6 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel006

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel007
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (110239637961024607937/100000000000000000000)
  centralHi := (55119818980512303969/50000000000000000000)
  directionLo := (60380736442455994057/50000000000000000000)
  directionHi := (24152294576982397623/20000000000000000000)

def endpointA : IntegerEndpointWitness 7 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree007.table
  base := (6156936675409117448774995583772510651909/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-735381145988218752315157542778620000000000000)
      constant := (3908176475416662539811141439265076798329645264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 7 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree007.table
  base := (12152521088291128817061352727166227944657/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-167332447744632116792828923740000000000000)
      constant := (883972794097587080857745897330484206007652) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 7 interval.damping) (curvature.centralUpper 7 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree007.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 7 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 7 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel007

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel008
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60380736442455994057/50000000000000000000)
  centralHi := (24152294576982397623/20000000000000000000)
  directionLo := (13043729868748773229/10000000000000000000)
  directionHi := (130437298687487732291/100000000000000000000)

def endpointA : IntegerEndpointWitness 8 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree008.table
  base := (4785486040353319009705837624216378291453/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-808024749427091855404903240634880000000000000)
      constant := (3918662897942970046753842403877453068998033488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 8 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree008.table
  base := (4717010362779503573173284756579747593301/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-183900993053423349454789103760000000000000)
      constant := (888549867938663545034235626313741826717672) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 8 interval.damping) (curvature.centralUpper 8 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree008.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 8 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 8 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel008

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel009
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13043729868748773229/10000000000000000000)
  centralHi := (130437298687487732291/100000000000000000000)
  directionLo := (34860834438919814499/25000000000000000000)
  directionHi := (139443337755679257997/100000000000000000000)

def endpointA : IntegerEndpointWitness 9 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree009.table
  base := (7348148491401229675586930570832573467967/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-293556117621988319498216312830380000000000000)
      constant := (1351306689665729997980352944345638464977738472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 9 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree009.table
  base := (3614323835379404578789504693343916859601/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-66823179454071527372249761260000000000000)
      constant := (307088169876250271382322941597754004630424) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 9 interval.damping) (curvature.centralUpper 9 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree009.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 9 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 9 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel009

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel010
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34860834438919814499/25000000000000000000)
  centralHi := (139443337755679257997/100000000000000000000)
  directionLo := (18487749322186300133/12500000000000000000)
  directionHi := (29580398915498080213/20000000000000000000)

def endpointA : IntegerEndpointWitness 10 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree010.table
  base := (5494027483379922684151330220316134149219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-953311956304838061584394636347400000000000000)
      constant := (4289872081750533459262074474857465504164983512) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 10 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree010.table
  base := (33676455266665754149692780815758972741/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-217038083671005814778709463800000000000000)
      constant := (976782632243784377470863705748771682988160) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 10 interval.damping) (curvature.centralUpper 10 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree010.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 10 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 10 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel010

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel011
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18487749322186300133/12500000000000000000)
  centralHi := (29580398915498080213/20000000000000000000)
  directionLo := (31180478223116178213/20000000000000000000)
  directionHi := (77951195557790445533/50000000000000000000)

def endpointA : IntegerEndpointWitness 11 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree011.table
  base := (783672965181807265723776900127958567481/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-1025955559743711164674140334203660000000000000)
      constant := (4612165771793269992121225640130944021203590440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 11 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree011.table
  base := (3824168430254837752605144960919006937041/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-233606628979797047440669643820000000000000)
      constant := (1051914354586781294143070746565584249733476) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 11 interval.damping) (curvature.centralUpper 11 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree011.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 11 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 11 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel011

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel012
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (31180478223116178213/20000000000000000000)
  centralHi := (77951195557790445533/50000000000000000000)
  directionLo := (163511807252904862237/100000000000000000000)
  directionHi := (81755903626452431119/50000000000000000000)

def endpointA : IntegerEndpointWitness 12 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree012.table
  base := (1281131332249871742180109485637139833859/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-366199721060861422587962010686640000000000000)
      constant := (1670477851054886872000153194280017210863737488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 12 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree012.table
  base := (309792584705803921575517450140561991721/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-83391724762862760034209941280000000000000)
      constant := (381522527148719239443276743893493951205216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 12 interval.damping) (curvature.centralUpper 12 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree012.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 12 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 12 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel012

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel013
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (163511807252904862237/100000000000000000000)
  centralHi := (81755903626452431119/50000000000000000000)
  directionLo := (170782512765993306387/100000000000000000000)
  directionHi := (42695628191498326597/25000000000000000000)

def endpointA : IntegerEndpointWitness 13 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree013.table
  base := (1384102642465235570497846564826775741389/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-1171242766621457370853631729916180000000000000)
      constant := (5481056109470381799728373739890095278116437672) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 13 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree013.table
  base := (20460698273898283189346003966631911737/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-266743719597379512764590003860000000000000)
      constant := (1253256776590688439637273515591619924642048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 13 interval.damping) (curvature.centralUpper 13 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree013.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 13 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 13 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel013

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel014
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170782512765993306387/100000000000000000000)
  centralHi := (42695628191498326597/25000000000000000000)
  directionLo := (17775607506417951459/10000000000000000000)
  directionHi := (177756075064179514591/100000000000000000000)

def endpointA : IntegerEndpointWitness 14 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree014.table
  base := (352665884199879533978927085287949739583/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-1243886370060330473943377427772440000000000000)
      constant := (6016068140983108817483019983786182830181196984) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 14 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree014.table
  base := (286533154031722109723922287392974031533/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-283312264906170745426550183880000000000000)
      constant := (1376863516792970949758164079556147065135188) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 14 interval.damping) (curvature.centralUpper 14 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree014.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 14 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 14 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel014

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel015
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (17775607506417951459/10000000000000000000)
  centralHi := (177756075064179514591/100000000000000000000)
  directionLo := (184466196843155461033/100000000000000000000)
  directionHi := (92233098421577730517/50000000000000000000)

def endpointA : IntegerEndpointWitness 15 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree015.table
  base := (-111283614942574278852267317612727784243/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-438843324499734525677707708542900000000000000)
      constant := (2204197858026106246246060154023936868952865560) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 15 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree015.table
  base := (-38426142833969571310141579081875657267/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-99960270071653992696170121300000000000000)
      constant := (504837615073042063919562440253779873804736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 15 interval.damping) (curvature.centralUpper 15 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree015.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 15 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 15 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel015

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel016
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184466196843155461033/100000000000000000000)
  centralHi := (92233098421577730517/50000000000000000000)
  directionLo := (190940653956493333607/100000000000000000000)
  directionHi := (23867581744561666701/12500000000000000000)

def endpointA : IntegerEndpointWitness 16 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree016.table
  base := (-1362645607279414340967855015828515790647/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-1389173576938076680122868823484960000000000000)
      constant := (7267531549622090113279330639904586220529175944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 16 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree016.table
  base := (-282805967411454416156962158335059272453/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-316449355523753210750470543920000000000000)
      constant := (1665504194364556133336445113259689330958460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 16 interval.damping) (curvature.centralUpper 16 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree016.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 16 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 16 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel016

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel017
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (190940653956493333607/100000000000000000000)
  centralHi := (23867581744561666701/12500000000000000000)
  directionLo := (39440531887330773617/20000000000000000000)
  directionHi := (98601329718326934043/50000000000000000000)

def endpointA : IntegerEndpointWitness 17 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree017.table
  base := (-1040919282547379682147877756774012330371/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-1461817180376949783212614521341220000000000000)
      constant := (7978365633761939781377013828002290023758306384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 17 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree017.table
  base := (-2126892930204374954922298733851500333317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-333017900832544443412430723940000000000000)
      constant := (1829269072781847245665008417133845988000588) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 17 interval.damping) (curvature.centralUpper 17 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree017.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 17 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 17 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel017

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel018
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39440531887330773617/20000000000000000000)
  centralHi := (98601329718326934043/50000000000000000000)
  directionLo := (203271848627507799433/100000000000000000000)
  directionHi := (101635924313753899717/50000000000000000000)

def endpointA : IntegerEndpointWitness 18 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree018.table
  base := (-1363470624218972227360340881898314578579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-511486927938607628767453406399160000000000000)
      constant := (2914345687142362436240686616646272908604111472) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 18 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree018.table
  base := (-2766318238139323356252030494198774502887/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-116528815380445225358130301320000000000000)
      constant := (668447565410079157133598127299614705965356) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 18 interval.damping) (curvature.centralUpper 18 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree018.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 18 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 18 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel018

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel019
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (203271848627507799433/100000000000000000000)
  centralHi := (101635924313753899717/50000000000000000000)
  directionLo := (104582503316759443497/50000000000000000000)
  directionHi := (41833001326703777399/20000000000000000000)

def endpointA : IntegerEndpointWitness 19 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree019.table
  base := (-3308591579603401118211721126404589087061/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-1607104387254695989392105917053740000000000000)
      constant := (9559853892352447953153097299307889164881122072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 19 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree019.table
  base := (-3342904852088719031622530856827973876863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-366154991450126908736351083980000000000000)
      constant := (2193343497425569147657256115326692940432932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 19 interval.damping) (curvature.centralUpper 19 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree019.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 19 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 19 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel019

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel020
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (104582503316759443497/50000000000000000000)
  centralHi := (41833001326703777399/20000000000000000000)
  directionLo := (10744830798523022293/5000000000000000000)
  directionHi := (214896615970460445861/100000000000000000000)

def endpointA : IntegerEndpointWitness 20 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree020.table
  base := (-3835553773933729064836731597686546707643/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-1679747990693569092481851614910000000000000000)
      constant := (10427422195616211915983253497511650119242796136) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 20 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree020.table
  base := (-773074756377453677531545420222114596887/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-382723536758918141398311264000000000000000)
      constant := (2392957520013792843795932235360019372560340) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 20 interval.damping) (curvature.centralUpper 20 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree020.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 20 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 20 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel020

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel021
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (10744830798523022293/5000000000000000000)
  centralHi := (214896615970460445861/100000000000000000000)
  directionLo := (1763834207376393727/800000000000000000)
  directionHi := (55119818980512303969/25000000000000000000)

def endpointA : IntegerEndpointWitness 21 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree021.table
  base := (-4315058189965035984292666486138780290129/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-584130531377480731857199104255420000000000000)
      constant := (3781530665717976113793869138246795174138520936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 21 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree021.table
  base := (-434090952461603544041593500004785054361/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-133097360689236458020090481340000000000000)
      constant := (867975374033330085079574458056925793476680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 21 interval.damping) (curvature.centralUpper 21 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree021.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 21 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 21 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel021

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel022
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1763834207376393727/800000000000000000)
  centralHi := (55119818980512303969/25000000000000000000)
  directionLo := (28240503566095748121/12500000000000000000)
  directionHi := (225924028528765984969/100000000000000000000)

def endpointA : IntegerEndpointWitness 22 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree022.table
  base := (-190122968286187033263035961327545311539/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-1825035197571315298661343010622520000000000000)
      constant := (12310413879101663997513895879691559332258628200) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 22 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree022.table
  base := (-4775434700016577981918674751635290121321/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-415860627376500606722231624040000000000000)
      constant := (2826036089373465301472854804631129555632444) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 22 interval.damping) (curvature.centralUpper 22 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree022.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 22 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 22 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel022

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel023
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (28240503566095748121/12500000000000000000)
  centralHi := (225924028528765984969/100000000000000000000)
  directionLo := (115620307712596732889/50000000000000000000)
  directionHi := (231240615425193465779/100000000000000000000)

def endpointA : IntegerEndpointWitness 23 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree023.table
  base := (-51545321378555118422167335551523038887/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-1897678801010188401751088708478780000000000000)
      constant := (13324103685140320692495495051463712621110042400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 23 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree023.table
  base := (-1293458359043775339372064834406825099509/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-432429172685291839384191804060000000000000)
      constant := (3059111593223114590066723259397917185670704) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 23 interval.damping) (curvature.centralUpper 23 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree023.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 23 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 23 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel023

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel024
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (115620307712596732889/50000000000000000000)
  centralHi := (231240615425193465779/100000000000000000000)
  directionLo := (118218841325925895933/50000000000000000000)
  directionHi := (236437682651851791867/100000000000000000000)

def endpointA : IntegerEndpointWitness 24 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree024.table
  base := (-5523504992620716916538737986897178481603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-656774134816353834946944802111680000000000000)
      constant := (4795004537029145794291914032384019185619335352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 24 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree024.table
  base := (-5540134242900707172031092272898889314031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-149665905998027690682050661360000000000000)
      constant := (1101002535765270154414566070645213328231628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 24 interval.damping) (curvature.centralUpper 24 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree024.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 24 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 24 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel024

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel025
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118218841325925895933/50000000000000000000)
  centralHi := (236437682651851791867/100000000000000000000)
  directionLo := (60380736442455994057/25000000000000000000)
  directionHi := (241522945769823976229/100000000000000000000)

def endpointA : IntegerEndpointWitness 25 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree025.table
  base := (-5863357956019561927036200418485853813701/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-2042966007887934607930580104191300000000000000)
      constant := (15492608431067640674926165484608318172638483352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 25 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree025.table
  base := (-5877660250294179519078747633028987406013/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-465566263302874304708112164100000000000000)
      constant := (3557604498907924693636642995523456453383532) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 25 interval.damping) (curvature.centralUpper 25 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree025.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 25 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 25 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel025

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel026
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60380736442455994057/25000000000000000000)
  centralHi := (241522945769823976229/100000000000000000000)
  directionLo := (123251662147908667553/50000000000000000000)
  directionHi := (246503324295817335107/100000000000000000000)

def endpointA : IntegerEndpointWitness 26 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree026.table
  base := (-7721089473158909457432282057692279123/12500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-2115609611326807711020325802047560000000000000)
      constant := (16646445904088969934707901789400831712036076800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 26 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree026.table
  base := (-3094576437222033935421978088662278859973/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-482134808611665537370072344120000000000000)
      constant := (3822803577080269500245899302826315922081944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 26 interval.damping) (curvature.centralUpper 26 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree026.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 26 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 26 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel026

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel027
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (123251662147908667553/50000000000000000000)
  centralHi := (246503324295817335107/100000000000000000000)
  directionLo := (251385052149972601437/100000000000000000000)
  directionHi := (125692526074986300719/50000000000000000000)

def endpointA : IntegerEndpointWitness 27 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree027.table
  base := (-808292928504076732691015058596716473721/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-729417738255226938036690499967940000000000000)
      constant := (5948720202191261225375391308727500585433659712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 27 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree027.table
  base := (-404804607292804903630345576027140096531/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-166234451306818923344010841380000000000000)
      constant := (1366174474721600886254716642220289101466048) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 27 interval.damping) (curvature.centralUpper 27 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree027.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 27 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 27 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel027

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel028
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (251385052149972601437/100000000000000000000)
  centralHi := (125692526074986300719/50000000000000000000)
  directionLo := (12808688457449497979/5000000000000000000)
  directionHi := (256173769148989959581/100000000000000000000)

def endpointA : IntegerEndpointWitness 28 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree028.table
  base := (-6733672022217198255866070648582959813837/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-2260896818204553917199817197760080000000000000)
      constant := (19091450583081925989372567175440997407528852824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 28 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree028.table
  base := (-3371344287515225396839385650800646381353/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-515271899229248002693992704160000000000000)
      constant := (4384696871433025946727883903182353460542584) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 28 interval.damping) (curvature.centralUpper 28 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree028.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 28 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 28 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel028

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel029
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (12808688457449497979/5000000000000000000)
  centralHi := (256173769148989959581/100000000000000000000)
  directionLo := (260874597374975464581/100000000000000000000)
  directionHi := (130437298687487732291/50000000000000000000)

def endpointA : IntegerEndpointWitness 29 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree029.table
  base := (-218138317348350034085608650841357742751/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-2333540421643427020289562895616340000000000000)
      constant := (20382066320054736756727687804772165729390046464) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 29 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree029.table
  base := (-6988136729039643681874214329898372237183/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-531840444538039235355952884180000000000000)
      constant := (4681268504820820447184082084096158599461412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 29 interval.damping) (curvature.centralUpper 29 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree029.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 29 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 29 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel029

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel030
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260874597374975464581/100000000000000000000)
  centralHi := (130437298687487732291/50000000000000000000)
  directionLo := (26549220536789985223/10000000000000000000)
  directionHi := (265492205367899852231/100000000000000000000)

def endpointA : IntegerEndpointWitness 30 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree030.table
  base := (-720790217084256935613544523910918456923/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-802061341694100041126436197824200000000000000)
      constant := (7239267212189510483109355513887262470877702320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 30 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree030.table
  base := (-225452752780472011704980315141429823373/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-182802996615610156005971021400000000000000)
      constant := (1662730869186243619688264681735690947824768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 30 interval.damping) (curvature.centralUpper 30 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree030.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 30 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 30 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel030

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel031
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (26549220536789985223/10000000000000000000)
  centralHi := (265492205367899852231/100000000000000000000)
  directionLo := (67507715608415210739/25000000000000000000)
  directionHi := (270030862433660842957/100000000000000000000)

def endpointA : IntegerEndpointWitness 31 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree031.table
  base := (-231786602634717649165000634453800162589/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-2478827628521173226469054291328860000000000000)
      constant := (23098486158018771485736143473614179985697431296) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 31 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree031.table
  base := (-3711395169538896265674671588987348249117/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-564977535155621700679873244220000000000000)
      constant := (5305431463014082634623876020465410926063576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 31 interval.damping) (curvature.centralUpper 31 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree031.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 31 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 31 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel031

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel032
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (67507715608415210739/25000000000000000000)
  centralHi := (270030862433660842957/100000000000000000000)
  directionLo := (137247242433338366711/50000000000000000000)
  directionHi := (274494484866676733423/100000000000000000000)

def endpointA : IntegerEndpointWitness 32 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree032.table
  base := (-3804559340869379316002812219500991492181/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-2551471231960046329558799989185120000000000000)
      constant := (24523979097312886885046651479280332610303192624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 32 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree032.table
  base := (-951738478583647042982514347022401430333/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-581546080464412933341833424240000000000000)
      constant := (5632953954611302918963152687897548388064096) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 32 interval.damping) (curvature.centralUpper 32 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree032.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 32 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 32 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel032

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel033
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137247242433338366711/50000000000000000000)
  centralHi := (274494484866676733423/100000000000000000000)
  directionLo := (34860834438919814499/12500000000000000000)
  directionHi := (278886675511358515993/100000000000000000000)

def endpointA : IntegerEndpointWitness 33 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree033.table
  base := (-3892237914496364126712269341145093839361/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-874704945132973144216181895680460000000000000)
      constant := (8664721372089232815963774828268662160024874448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 33 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree033.table
  base := (-3894276828195057619468416354384099156469/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-199371541924401388667931201420000000000000)
      constant := (1990244803599773590905399575212281620244744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 33 interval.damping) (curvature.centralUpper 33 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree033.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 33 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 33 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel033

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel034
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34860834438919814499/12500000000000000000)
  centralHi := (278886675511358515993/100000000000000000000)
  directionLo := (141605378899720237051/50000000000000000000)
  directionHi := (283210757799440474103/100000000000000000000)

def endpointA : IntegerEndpointWitness 34 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree034.table
  base := (-7943847168583211992058385356440156648207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-2696758438837792535738291384897640000000000000)
      constant := (27508945079510821879660207502795010965415973064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 34 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree034.table
  base := (-7947316139292151177925608008544974458649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-614683171081995398665753784280000000000000)
      constant := (6318751652164280685274554136502380919488636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 34 interval.damping) (curvature.centralUpper 34 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree034.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 34 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 34 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel034

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel035
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (141605378899720237051/50000000000000000000)
  centralHi := (283210757799440474103/100000000000000000000)
  directionLo := (287469805177672336503/100000000000000000000)
  directionHi := (35933725647209042063/12500000000000000000)

def endpointA : IntegerEndpointWitness 35 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree035.table
  base := (-8087732179925744167115077099822725889369/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-2769402042276665638828037082753900000000000000)
      constant := (29068242545840175277951920443939801342747639288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 35 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree035.table
  base := (-4045340324827335176399020621321086134109/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-631251716390786631327713964300000000000000)
      constant := (6676988205304124753727241300077381798344152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 35 interval.damping) (curvature.centralUpper 35 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree035.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 35 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 35 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel035

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel036
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (287469805177672336503/100000000000000000000)
  centralHi := (35933725647209042063/12500000000000000000)
  directionLo := (145833333333333333333/50000000000000000000)
  directionHi := (291666666666666666667/100000000000000000000)

def endpointA : IntegerEndpointWitness 36 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree036.table
  base := (-8216543608280278609283893505173898953261/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-947348548571846247305927593536720000000000000)
      constant := (10223996956315884501967664922524960573093914824) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 36 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree036.table
  base := (-2054761907567795131547736873927071502223/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-215940087233192621329891381440000000000000)
      constant := (2348476551426095566206444957771500567893296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 36 interval.damping) (curvature.centralUpper 36 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree036.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 36 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 36 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel036

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel037
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (145833333333333333333/50000000000000000000)
  centralHi := (291666666666666666667/100000000000000000000)
  directionLo := (18487749322186300133/6250000000000000000)
  directionHi := (295803989154980802129/100000000000000000000)

def endpointA : IntegerEndpointWitness 37 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree037.table
  base := (-4165311263903817376286680601646875598393/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-2914689249154411845007528478466420000000000000)
      constant := (32320135801670126554173242330124761709653580272) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 37 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree037.table
  base := (-8332747457013027429281580339549864613149/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-664388807008369096651634324340000000000000)
      constant := (7424064105555398073628453727628704873926636) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 37 interval.damping) (curvature.centralUpper 37 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree037.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 37 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 37 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel037

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel038
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18487749322186300133/6250000000000000000)
  centralHi := (295803989154980802129/100000000000000000000)
  directionLo := (74971059231027423321/25000000000000000000)
  directionHi := (59976847384821938657/20000000000000000000)

def endpointA : IntegerEndpointWitness 38 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree038.table
  base := (-1053781348573239600970181718431397639137/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-2987332852593284948097274176322680000000000000)
      constant := (34012632516316372104246847993889129546324307392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 38 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree038.table
  base := (-4216026350207129028446038570514635753319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-680957352317160329313594504360000000000000)
      constant := (7812881746596233186941000917812946225761032) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 38 interval.damping) (curvature.centralUpper 38 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree038.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 38 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 38 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel038

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel039
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74971059231027423321/25000000000000000000)
  centralHi := (59976847384821938657/20000000000000000000)
  directionLo := (303909708813507817343/100000000000000000000)
  directionHi := (2374294600105529823/781250000000000000)

def endpointA : IntegerEndpointWitness 39 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree039.table
  base := (-106445766274071814325664926156060335581/125000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-1019992152010719350395673291392980000000000000)
      constant := (11916481322936086202441465089315603169907016320) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 39 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree039.table
  base := (-2129297060364179068692921268332442028521/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-232508632541983853991851561460000000000000)
      constant := (2737291493895148553130001181877542782630992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 39 interval.damping) (curvature.centralUpper 39 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree039.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 39 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 39 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel039

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel040
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (303909708813507817343/100000000000000000000)
  centralHi := (2374294600105529823/781250000000000000)
  directionLo := (30788255336518609993/10000000000000000000)
  directionHi := (307882553365186099931/100000000000000000000)

def endpointA : IntegerEndpointWitness 40 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree040.table
  base := (-1717409307882572211964140443153767324641/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-3132620059471031154276765572035200000000000000)
      constant := (37530539546925017082336683214136398072752491160) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 40 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree040.table
  base := (-8588339617074429901622659029718820598477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-714094442934742794637514864400000000000000)
      constant := (8621035631493410489502180434930122458454828) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 40 interval.damping) (curvature.centralUpper 40 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree040.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 40 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 40 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel040

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel041
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30788255336518609993/10000000000000000000)
  centralHi := (307882553365186099931/100000000000000000000)
  directionLo := (311804782231161782131/100000000000000000000)
  directionHi := (77951195557790445533/25000000000000000000)

def endpointA : IntegerEndpointWitness 41 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree041.table
  base := (-8644565555903889063709161519235617955209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-3205263662909904257366511269891460000000000000)
      constant := (39355893953309811113478424702747349685459918968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 41 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree041.table
  base := (-4322829952589593129079733717615701965557/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-730662988243534027299475044420000000000000)
      constant := (9040359685215303333731810722404169458479896) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 41 interval.damping) (curvature.centralUpper 41 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree041.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 41 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 41 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel041

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel042
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (311804782231161782131/100000000000000000000)
  centralHi := (77951195557790445533/25000000000000000000)
  directionLo := (39459785260157939407/12500000000000000000)
  directionHi := (315678282081263515257/100000000000000000000)

def endpointA : IntegerEndpointWitness 42 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree042.table
  base := (-8688349792823305606434507559688637445879/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-1092635755449592453485418989249240000000000000)
      constant := (13741828760822320190178082538447062197169278936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 42 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree042.table
  base := (-2172318851198358209510227797680821033017/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-249077177850775086653811741480000000000000)
      constant := (3156614032028772027435725858541320590415184) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 42 interval.damping) (curvature.centralUpper 42 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree042.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 42 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 42 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel042

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel043
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (39459785260157939407/12500000000000000000)
  centralHi := (315678282081263515257/100000000000000000000)
  directionLo := (79876206302836724879/25000000000000000000)
  directionHi := (319504825211346899517/100000000000000000000)

def endpointA : IntegerEndpointWitness 43 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree043.table
  base := (-4359253936794675534881547567325972646839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-3350550869787650463546002665603980000000000000)
      constant := (43139299258059041157264976754081303654931101456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 43 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree043.table
  base := (-871929032214893295762168090202961893403/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-763800078861116492623395404460000000000000)
      constant := (9909479112682105255839512132779433718374920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 43 interval.damping) (curvature.centralUpper 43 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree043.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 43 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 43 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel043

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel044
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (79876206302836724879/25000000000000000000)
  centralHi := (319504825211346899517/100000000000000000000)
  directionLo := (323286079021180386007/100000000000000000000)
  directionHi := (40410759877647548251/12500000000000000000)

def endpointA : IntegerEndpointWitness 44 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree044.table
  base := (-4367564783104151790818972915220852152561/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-3423194473226523566635748363460240000000000000)
      constant := (45097318602664190349977530421707287813678956144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 44 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree044.table
  base := (-4367895318354654831064843201672455817073/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-780368624169907725285355584480000000000000)
      constant := (10359267639741980424700609639839583181170744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 44 interval.damping) (curvature.centralUpper 44 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree044.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 44 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 44 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel044

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel045
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (323286079021180386007/100000000000000000000)
  centralHi := (40410759877647548251/12500000000000000000)
  directionLo := (13080944580232388979/4000000000000000000)
  directionHi := (81755903626452431119/25000000000000000000)

def endpointA : IntegerEndpointWitness 45 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree045.table
  base := (-8738289057677270250462656209456620560987/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-1165279358888465556575164687105500000000000000)
      constant := (15699844172329630752431511130720916554338713208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 45 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree045.table
  base := (-1747769458126369750884691611966912127693/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-265645723159566319315771921500000000000000)
      constant := (3606401707782759766662521001219485272338420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 45 interval.damping) (curvature.centralUpper 45 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree045.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 45 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 45 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel045

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel046
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (13080944580232388979/4000000000000000000)
  centralHi := (81755903626452431119/25000000000000000000)
  directionLo := (82679728470768455953/25000000000000000000)
  directionHi := (330718913883073823813/100000000000000000000)

def endpointA : IntegerEndpointWitness 46 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree046.table
  base := (-174560953194316364734048378155816287221/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-3568481680104269772815239759172760000000000000)
      constant := (49145931249526773161478317707062191557503719600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 46 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree046.table
  base := (-436425941003430880674235131058934098361/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-813505714787490190609275944520000000000000)
      constant := (11289289456199527456057030781247567449180080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 46 interval.damping) (curvature.centralUpper 46 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree046.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 46 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 46 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel046

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel047
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (82679728470768455953/25000000000000000000)
  centralHi := (330718913883073823813/100000000000000000000)
  directionLo := (167186688731157328609/50000000000000000000)
  directionHi := (334373377462314657219/100000000000000000000)

def endpointA : IntegerEndpointWitness 47 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree047.table
  base := (-8704456044589480538710215141843576589031/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 720000000000000000000000000000000000000000
      center := (1959)
      previous := (0)
      next := (1425)
      square := (28403220529356398849074594320000000000000)
      linear := (-1648313844971997680355357834780000000000000)
      constant := (23194434921211111168042932734223512485589768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 47 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree047.table
  base := (-4352426762993395931433249885414851356481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-830074260096281423271236124540000000000000)
      constant := (11769518899460906570461102104002630702333368) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 47 interval.damping) (curvature.centralUpper 47 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree047.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 47 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 47 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel047

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel048
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (167186688731157328609/50000000000000000000)
  centralHi := (334373377462314657219/100000000000000000000)
  directionLo := (168994164922277058417/50000000000000000000)
  directionHi := (67597665968910823367/20000000000000000000)

def endpointA : IntegerEndpointWitness 48 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree048.table
  base := (-8667556092635791786035435020202852028317/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-1237922962327338659664910384961760000000000000)
      constant := (17790417443430227425239841367561565596866745928) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 48 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree048.table
  base := (-8667891265093926667135836791576274221361/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-282214268468357551977732101520000000000000)
      constant := (4086630672763648219091788476581084709343668) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 48 interval.damping) (curvature.centralUpper 48 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree048.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 48 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 48 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel048

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel049
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (168994164922277058417/50000000000000000000)
  centralHi := (67597665968910823367/20000000000000000000)
  directionLo := (170782512765993306387/50000000000000000000)
  directionHi := (13662601021279464511/4000000000000000000)

def endpointA : IntegerEndpointWitness 49 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree049.table
  base := (-134646600295780957343594361214011609879/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-3786412490420889082084476852741540000000000000)
      constant := (55550162512074301209691790079911804664205747712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 49 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree049.table
  base := (-8617664927351222666455838011469414169421/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-863211350713863888595156484580000000000000)
      constant := (12760407628651038493453948282659601089900844) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 49 interval.damping) (curvature.centralUpper 49 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree049.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 49 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 49 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel049

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel050
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (170782512765993306387/50000000000000000000)
  centralHi := (13662601021279464511/4000000000000000000)
  directionLo := (345104654014144269149/100000000000000000000)
  directionHi := (6902093080282885383/2000000000000000000)

def endpointA : IntegerEndpointWitness 50 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree050.table
  base := (-4276981817407721894585722189936820492023/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-3859056093859762185174222550597800000000000000)
      constant := (57773232735729257116196314371225482148769451792) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 50 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree050.table
  base := (-8554201654923120056614435764388605182509/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-879779896022655121257116664600000000000000)
      constant := (13271064753423268231948485098732010213429676) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 50 interval.damping) (curvature.centralUpper 50 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree050.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 50 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 50 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel050

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel051
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (345104654014144269149/100000000000000000000)
  centralHi := (6902093080282885383/2000000000000000000)
  directionLo := (34860834438919814499/10000000000000000000)
  directionHi := (348608344389198144991/100000000000000000000)

def endpointA : IntegerEndpointWitness 51 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree051.table
  base := (-8477323390346136465786439767131649511199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-1310566565766211762754656082818020000000000000)
      constant := (20013486413253922740953450535350777219514273816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 51 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree051.table
  base := (-2119380961953229906936200757170668535097/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-298782813777148784639692281540000000000000)
      constant := (4597287528735838348104727216913307910315344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 51 interval.damping) (curvature.centralUpper 51 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree051.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 51 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 51 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel051

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel052
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (34860834438919814499/10000000000000000000)
  centralHi := (348608344389198144991/100000000000000000000)
  directionLo := (70415433914258693101/20000000000000000000)
  directionHi := (176038584785646732753/50000000000000000000)

def endpointA : IntegerEndpointWitness 52 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree052.table
  base := (-8387481235690864223579054743394532323487/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-4004343300737508391353713946310320000000000000)
      constant := (62351838914756586444172261386214206423014039624) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 52 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree052.table
  base := (-8387649993515266590222550032874015500823/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-912916986640237586581037024640000000000000)
      constant := (14322800461453971702977515970456535441970372) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 52 interval.damping) (curvature.centralUpper 52 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree052.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 52 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 52 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel052

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel053
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (70415433914258693101/20000000000000000000)
  centralHi := (176038584785646732753/50000000000000000000)
  directionLo := (355512150128359029181/100000000000000000000)
  directionHi := (177756075064179514591/50000000000000000000)

def endpointA : IntegerEndpointWitness 53 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree053.table
  base := (-4142226666470558899413756889359665467591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-4076986904176381494443459644166580000000000000)
      constant := (64707369190165384361508464666197474103421173264) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 53 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree053.table
  base := (-2071148837870821055071319450822029575141/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-929485531949028819242997204660000000000000)
      constant := (14863877829822325769993934420934127741179696) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 53 interval.damping) (curvature.centralUpper 53 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree053.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 53 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 53 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel053

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel054
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (355512150128359029181/100000000000000000000)
  centralHi := (177756075064179514591/50000000000000000000)
  directionLo := (1794571288946502429/500000000000000000)
  directionHi := (358914257789300485801/100000000000000000000)

def endpointA : IntegerEndpointWitness 54 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree054.table
  base := (-8168253044303508860375968715966181670861/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-1383210169205084865844401780674280000000000000)
      constant := (22369015980251974934054212261232971912537633224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 54 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree054.table
  base := (-4084186258909196765527829601509948127837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-315351359085940017301652461560000000000000)
      constant := (5138364745950975362963673593033761244931912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 54 interval.damping) (curvature.centralUpper 54 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree054.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 54 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 54 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel054

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel055
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1794571288946502429/500000000000000000)
  centralHi := (358914257789300485801/100000000000000000000)
  directionLo := (181142209327367982171/50000000000000000000)
  directionHi := (362284418654735964343/100000000000000000000)

def endpointA : IntegerEndpointWitness 55 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree055.table
  base := (-8038891418145589543428649532972030185497/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-4222274111054127700622951039879100000000000000)
      constant := (69550873409307445334134815369203520793057073144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 55 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree055.table
  base := (-502436993196520345446325900128683965529/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-962622622566611284566917564700000000000000)
      constant := (15976449311195318343502904318838378035855296) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 55 interval.damping) (curvature.centralUpper 55 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree055.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 55 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 55 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel055

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel056
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (181142209327367982171/50000000000000000000)
  centralHi := (362284418654735964343/100000000000000000000)
  directionLo := (365623516141338419183/100000000000000000000)
  directionHi := (22851469758833651199/6250000000000000000)

def endpointA : IntegerEndpointWitness 56 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree056.table
  base := (-7896377590635245866405459725493557576617/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-4294917714493000803712696737735360000000000000)
      constant := (72038844142730716021967351611518180654554219384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 56 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree056.table
  base := (-7896462056958460154792005429423359753613/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-979191167875402517228877744720000000000000)
      constant := (16547942740771596855764582807100759048869932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 56 interval.damping) (curvature.centralUpper 56 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree056.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 56 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 56 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel056

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel057
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (365623516141338419183/100000000000000000000)
  centralHi := (22851469758833651199/6250000000000000000)
  directionLo := (184466196843155461033/50000000000000000000)
  directionHi := (368932393686310922067/100000000000000000000)

def endpointA : IntegerEndpointWitness 57 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree057.table
  base := (-7740719117632817051378248513629847347999/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-1455853772643957968934147478530540000000000000)
      constant := (24856986313093753877689387345294858762998485016) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 57 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree057.table
  base := (-3870395052363616310335957922839751114999/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-331919904394731249963612641580000000000000)
      constant := (5709858090453656652745385478569345973240024) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 57 interval.damping) (curvature.centralUpper 57 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree057.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 57 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 57 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel057

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel058
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (184466196843155461033/50000000000000000000)
  centralHi := (368932393686310922067/100000000000000000000)
  directionLo := (46526482154431863587/12500000000000000000)
  directionHi := (372211857235454908697/100000000000000000000)

def endpointA : IntegerEndpointWitness 58 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree058.table
  base := (-473245140559322048028035733439688766323/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-4440204921370747009892188133447880000000000000)
      constant := (77147216804939166149106934389435495097501751936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 58 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree058.table
  base := (-3785990944747793028621745164172322510667/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1012328258492984982552798104760000000000000)
      constant := (17721343692181819698148973596269592779231976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 58 interval.damping) (curvature.centralUpper 58 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree058.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 58 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 58 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel058

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel059
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (46526482154431863587/12500000000000000000)
  centralHi := (372211857235454908697/100000000000000000000)
  directionLo := (1877313387678134989/500000000000000000)
  directionHi := (375462677535626997801/100000000000000000000)

def endpointA : IntegerEndpointWitness 59 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree059.table
  base := (-7389992154979046169970502255367494681749/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-4512848524809620112981933831304140000000000000)
      constant := (79767616917363478508788058091033696955857185048) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 59 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree059.table
  base := (-369502112386031646560878027842144030149/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1028896803801776215214758284780000000000000)
      constant := (18323250829121690026701444348326156298292720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 59 interval.damping) (curvature.centralUpper 59 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree059.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 59 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 59 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel059

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel060
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1877313387678134989/500000000000000000)
  centralHi := (375462677535626997801/100000000000000000000)
  directionLo := (47335699031257347407/12500000000000000000)
  directionHi := (378685592250058779257/100000000000000000000)

def endpointA : IntegerEndpointWitness 60 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree060.table
  base := (-7194933113981080072511194992750022861303/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-1528497376082831072023893176386800000000000000)
      constant := (27477386198701909210767386761753864787985160152) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 60 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree060.table
  base := (-7194975175340349597110860795519179567009/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-348488449703522482625572821600000000000000)
      constant := (6311765179442271265043655419453769845195892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 60 interval.damping) (curvature.centralUpper 60 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree060.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 60 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 60 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel060

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel061
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (47335699031257347407/12500000000000000000)
  centralHi := (378685592250058779257/100000000000000000000)
  directionLo := (76376261582597333443/20000000000000000000)
  directionHi := (23867581744561666701/6250000000000000000)

def endpointA : IntegerEndpointWitness 61 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree061.table
  base := (-3493374333419220554311894446618337159589/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-4658135731687366319161425227016660000000000000)
      constant := (85140841277995524452114929329027179672883377456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 61 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree061.table
  base := (-698678397468618410673993156233897091303/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1062033894419358680538678644820000000000000)
      constant := (19557477700913258873572143867728297047130920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 61 interval.damping) (curvature.centralUpper 61 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree061.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 61 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 61 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel061

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel062
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (76376261582597333443/20000000000000000000)
  centralHi := (23867581744561666701/6250000000000000000)
  directionLo := (385050501738264053503/100000000000000000000)
  directionHi := (1504103522415093959/390625000000000000)

def endpointA : IntegerEndpointWitness 62 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree062.table
  base := (-169136043623706420924215354836605070809/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-4730779335126239422251170924872920000000000000)
      constant := (87893664496800018624276557018853850467918806720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 62 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree062.table
  base := (-1691367843922965451575027088101528513549/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1078602439728149913200638824840000000000000)
      constant := (20189797218603411149561945098603379894048944) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 62 interval.damping) (curvature.centralUpper 62 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree062.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 62 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 62 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel062

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel063
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (385050501738264053503/100000000000000000000)
  centralHi := (1504103522415093959/390625000000000000)
  directionLo := (194096911647535265751/50000000000000000000)
  directionHi := (388193823295070531503/100000000000000000000)

def endpointA : IntegerEndpointWitness 63 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree063.table
  base := (-6531014775906164909505524202131322865351/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-1601140979521704175113638874243060000000000000)
      constant := (30230209288804993057172710868566564536970551384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 63 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree063.table
  base := (-816379954487061166251573786156270303117/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-365056995012313715287533001620000000000000)
      constant := (6944084670041954261422802260846498050900768) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 63 interval.damping) (curvature.centralUpper 63 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree063.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 63 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 63 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel063

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel064
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (194096911647535265751/50000000000000000000)
  centralHi := (388193823295070531503/100000000000000000000)
  directionLo := (391311896062463196871/100000000000000000000)
  directionHi := (48913987007807899609/12500000000000000000)

def endpointA : IntegerEndpointWitness 64 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree064.table
  base := (-785433721355290960569362146274349424131/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-4876066542003985628430662320585440000000000000)
      constant := (93531731066974176031073516569506538182326501696) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 64 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree064.table
  base := (-6283490622952862338591037468609530068901/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1111739530345732378524559184880000000000000)
      constant := (21484848008245113133905837156090056917519564) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 64 interval.damping) (curvature.centralUpper 64 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree064.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 64 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 64 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel064

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel065
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (391311896062463196871/100000000000000000000)
  centralHi := (48913987007807899609/12500000000000000000)
  directionLo := (394405318873307736171/100000000000000000000)
  directionHi := (98601329718326934043/25000000000000000000)

def endpointA : IntegerEndpointWitness 65 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree065.table
  base := (-3011404198297687257043663035840231843709/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-4948710145442858731520408018441700000000000000)
      constant := (96416973833370258881770490038941521861443541936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 65 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree065.table
  base := (-3011412941351225932301644493717756191477/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1128308075654523611186519364900000000000000)
      constant := (22147579157310869241301794011764821554213656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 65 interval.damping) (curvature.centralUpper 65 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree065.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 65 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 65 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel065

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel066
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (394405318873307736171/100000000000000000000)
  centralHi := (98601329718326934043/25000000000000000000)
  directionLo := (198737333628530343573/50000000000000000000)
  directionHi := (397474667257060687147/100000000000000000000)

def endpointA : IntegerEndpointWitness 66 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree066.table
  base := (-2874516017678669961203557736140161401643/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-1673784582960577278203384572099320000000000000)
      constant := (33115451981922783005529167327146821406260989424) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 66 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree066.table
  base := (-5749046695342768793160133290556409083839/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-381625540321104947949493181640000000000000)
      constant := (7606815803745340238197429655183323090993932) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 66 interval.damping) (curvature.centralUpper 66 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree066.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 66 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 66 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel066

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel067
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (198737333628530343573/50000000000000000000)
  centralHi := (397474667257060687147/100000000000000000000)
  directionLo := (40052049468993052599/10000000000000000000)
  directionHi := (400520494689930525991/100000000000000000000)

def endpointA : IntegerEndpointWitness 67 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree067.table
  base := (-5462141833965367501788904429784996803719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-5093997352320604937699899414154220000000000000)
      constant := (102319877221766292421460455604139882078362100488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 67 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree067.table
  base := (-5462154121770795470635365636317798292211/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1161445166272106076510439724940000000000000)
      constant := (23503452731828276189307865388145059261480404) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 67 interval.damping) (curvature.centralUpper 67 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree067.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 67 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 67 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel067

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel068
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (40052049468993052599/10000000000000000000)
  centralHi := (400520494689930525991/100000000000000000000)
  directionLo := (4035433337601083731/1000000000000000000)
  directionHi := (403543333760108373101/100000000000000000000)

def endpointA : IntegerEndpointWitness 68 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree068.table
  base := (-5162138744638073534138307639770408626079/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-5166640955759478040789645112010480000000000000)
      constant := (105337537509915622613984826700937816048839387208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 68 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree068.table
  base := (-2581074520910759116788395354238043142837/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1178013711580897309172399904960000000000000)
      constant := (24196595087413576157332802310934860893715736) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 68 interval.damping) (curvature.centralUpper 68 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree068.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 68 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 68 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel068

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel069
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4035433337601083731/1000000000000000000)
  centralHi := (403543333760108373101/100000000000000000000)
  directionLo := (406543697255015598867/100000000000000000000)
  directionHi := (101635924313753899717/25000000000000000000)

def endpointA : IntegerEndpointWitness 69 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree069.table
  base := (-242451177932110861110819686595433145313/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-1746428186399450381293130269955580000000000000)
      constant := (36133112228122314692159957609474059077361719840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 69 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree069.table
  base := (-4849032185819757052527254932626966324691/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-398194085629896180611453361660000000000000)
      constant := (8299958150566742366575852420865976404103708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 69 interval.damping) (curvature.centralUpper 69 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree069.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 69 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 69 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel069

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel070
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (406543697255015598867/100000000000000000000)
  centralHi := (101635924313753899717/25000000000000000000)
  directionLo := (409522079176853825141/100000000000000000000)
  directionHi := (204761039588426912571/50000000000000000000)

def endpointA : IntegerEndpointWitness 70 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree070.table
  base := (-4522796934117307751629062523224796035717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-5311928162637224246969136507723000000000000000)
      constant := (111505274640444484151993346832494767640111282584) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 70 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree070.table
  base := (-2261402080307649965501639624205139476579/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1211150802198479774496320265000000000000000)
      constant := (25613290802841636648365535489307229957686312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 70 interval.damping) (curvature.centralUpper 70 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree070.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 70 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 70 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel070

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel071
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (409522079176853825141/100000000000000000000)
  centralHi := (204761039588426912571/50000000000000000000)
  directionLo := (412478955692152722567/100000000000000000000)
  directionHi := (51559869461519090321/12500000000000000000)

def endpointA : IntegerEndpointWitness 71 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree071.table
  base := (-2091729709536286786807840665975656173553/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-5384571766076097350058882205579260000000000000)
      constant := (114655351290988471073812529819925343923817484912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 71 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree071.table
  base := (-4183465471066596188826979815322607373871/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1227719347507271007158280445020000000000000)
      constant := (26336844122662900627733140809320886134540644) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 71 interval.damping) (curvature.centralUpper 71 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree071.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 71 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 71 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel071

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel072
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (412478955692152722567/100000000000000000000)
  centralHi := (51559869461519090321/12500000000000000000)
  directionLo := (103853696505120980589/25000000000000000000)
  directionHi := (415414786020483922357/100000000000000000000)

def endpointA : IntegerEndpointWitness 72 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree072.table
  base := (-1915505735197271729620286413525768272449/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-1819071789838323484382875967811840000000000000)
      constant := (39283188854444005404652394466286875738535687632) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 72 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree072.table
  base := (-3831016537769342798139915020219251516437/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-414762630938687413273413541680000000000000)
      constant := (9023511465340857982277759040237368981802756) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 72 interval.damping) (curvature.centralUpper 72 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree072.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 72 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 72 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel072

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel073
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (103853696505120980589/25000000000000000000)
  centralHi := (415414786020483922357/100000000000000000000)
  directionLo := (418330013267037773989/100000000000000000000)
  directionHi := (41833001326703777399/10000000000000000000)

def endpointA : IntegerEndpointWitness 73 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree073.table
  base := (-3465453469557910886373512840901715791561/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-5529858972953843556238373601291780000000000000)
      constant := (121087920396802332524159075462712840156783806072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 73 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree073.table
  base := (-3465457711686940348134226546866799545103/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1260856438124853472482200805060000000000000)
      constant := (27814361610285974184455027322865295216376292) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 73 interval.damping) (curvature.centralUpper 73 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree073.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 73 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 73 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel073

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel074
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (418330013267037773989/100000000000000000000)
  centralHi := (41833001326703777399/10000000000000000000)
  directionLo := (421225065203337057487/100000000000000000000)
  directionHi := (26326566575208566093/6250000000000000000)

def endpointA : IntegerEndpointWitness 74 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree074.table
  base := (-123471429424482359310668260572241220733/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-5602502576392716659328119299148040000000000000)
      constant := (124370412740655253716715473288247359458121445400) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 74 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree074.table
  base := (-3086789286224826310600500163737882584003/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1277424983433644705144160985080000000000000)
      constant := (28568325754890505591613930328115436226975892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 74 interval.damping) (curvature.centralUpper 74 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree074.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 74 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 74 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel074

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel075
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (421225065203337057487/100000000000000000000)
  centralHi := (26326566575208566093/6250000000000000000)
  directionLo := (106025088749995604257/25000000000000000000)
  directionHi := (424100354999982417029/100000000000000000000)

def endpointA : IntegerEndpointWitness 75 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree075.table
  base := (-2695008535916221319929844722652473378579/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-1891715393277196587472621665668100000000000000)
      constant := (42565681184122609470181634520371825221361255736) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 75 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree075.table
  base := (-1347505753597922407960312414543632011263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-431331176247478645935373721700000000000000)
      constant := (9777475606995635259872079377988452831729688) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 75 interval.damping) (curvature.centralUpper 75 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree075.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 75 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 75 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel075

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel076
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (106025088749995604257/25000000000000000000)
  centralHi := (424100354999982417029/100000000000000000000)
  directionLo := (426956281914983265967/100000000000000000000)
  directionHi := (26684767619686454123/6250000000000000000)

def endpointA : IntegerEndpointWitness 76 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree076.table
  base := (-2290122095014115753970616671182252212209/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-5747789783270462865507610694860560000000000000)
      constant := (131067812796226827368069150528601985150152582968) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 76 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree076.table
  base := (-7156639315767383933912155743936313479/31250000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1310562074051227170468081345120000000000000)
      constant := (30106664801143134336650688325789853668721920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 76 interval.damping) (curvature.centralUpper 76 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree076.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 76 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 76 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel076

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel077
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (426956281914983265967/100000000000000000000)
  centralHi := (26684767619686454123/6250000000000000000)
  directionLo := (429793231940920891721/100000000000000000000)
  directionHi := (214896615970460445861/50000000000000000000)

def endpointA : IntegerEndpointWitness 77 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree077.table
  base := (-117007912623188491736015607005512757783/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-5820433386709335968597356392716820000000000000)
      constant := (134482720442161796956477166454795321560402070656) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 77 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree077.table
  base := (-46803217041047192954526313274668515857/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1327130619360018403130041525140000000000000)
      constant := (30891039689099946600680957639336977337165920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 77 interval.damping) (curvature.centralUpper 77 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree077.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 77 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 77 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel077

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel078
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (429793231940920891721/100000000000000000000)
  centralHi := (214896615970460445861/50000000000000000000)
  directionLo := (54076447301739209001/12500000000000000000)
  directionHi := (432611578413913672009/100000000000000000000)

def endpointA : IntegerEndpointWitness 78 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree078.table
  base := (-9006388852750873528703783956001814769/62500000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-1964358996716069690562367363524360000000000000)
      constant := (45980588821593404047627967848637492246113071360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 78 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree078.table
  base := (-1441023955880082780922093571214019733933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-447899721556269878597333901720000000000000)
      constant := (10561850493189704363258180923575431763192804) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 78 interval.damping) (curvature.centralUpper 78 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree078.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 78 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 78 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel078

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel079
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54076447301739209001/12500000000000000000)
  centralHi := (432611578413913672009/100000000000000000000)
  directionLo := (54426460323388047181/12500000000000000000)
  directionHi := (435411682587104377449/100000000000000000000)

def endpointA : IntegerEndpointWitness 79 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree079.table
  base := (-996809073678891687948901681988578520621/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-5965720593587082174776847788429340000000000000)
      constant := (141444950842569653297164526761634516813452271192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 79 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree079.table
  base := (-498405264155170863395118525023706654839/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1360267709977600868453961885180000000000000)
      constant := (32490200168066826831461695652670793120851592) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 79 interval.damping) (curvature.centralUpper 79 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree079.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 79 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 79 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel079

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel080
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (54426460323388047181/12500000000000000000)
  centralHi := (435411682587104377449/100000000000000000000)
  directionLo := (438193894171163559001/100000000000000000000)
  directionHi := (219096947085581779501/50000000000000000000)

def endpointA : IntegerEndpointWitness 80 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree080.table
  base := (-107897457739439292876683332639010751509/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-6038364197025955277866593486285600000000000000)
      constant := (144992273557238021895507776030168153089969982840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 80 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree080.table
  base := (-21579540198353319809207758321620258241/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1376836255286392101115922065200000000000000)
      constant := (33304985750776145761922406689510541767583100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 80 interval.damping) (curvature.centralUpper 80 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree080.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 80 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 80 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel080

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel081
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (438193894171163559001/100000000000000000000)
  centralHi := (219096947085581779501/50000000000000000000)
  directionLo := (1763834207376393727/400000000000000000)
  directionHi := (440958551844098431751/100000000000000000000)

def endpointA : IntegerEndpointWitness 81 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree081.table
  base := (-34528479844261085471711984570252436833/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-2037002600154942793652113061380620000000000000)
      constant := (49527911531055947742398478860387925743617723344) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 81 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree081.table
  base := (-17264494120805484339354418112763275919/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-464468266865061111259294081740000000000000)
      constant := (11376636074811131309505506519888087362755888) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 81 interval.damping) (curvature.centralUpper 81 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree081.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 81 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 81 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel081

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel082
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (1763834207376393727/400000000000000000)
  centralHi := (440958551844098431751/100000000000000000000)
  directionLo := (55463247966558900399/12500000000000000000)
  directionHi := (443705983732471203193/100000000000000000000)

def endpointA : IntegerEndpointWitness 82 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree082.table
  base := (20724091456598120193351543693317753089/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-6183651403903701484046084881998120000000000000)
      constant := (152219333936964863126753516981753041039865985440) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 82 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree082.table
  base := (414480979220993129649420809819293575747/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1409973345903974566439842425240000000000000)
      constant := (34964967586234333391825602107243494568726892) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 82 interval.damping) (curvature.centralUpper 82 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree082.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 82 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 82 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel082

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel083
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (55463247966558900399/12500000000000000000)
  centralHi := (443705983732471203193/100000000000000000000)
  directionLo := (44643650786596245343/10000000000000000000)
  directionHi := (446436507865962453431/100000000000000000000)

def endpointA : IntegerEndpointWitness 83 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree083.table
  base := (91112900517925650963483477668276275719/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-6256295007342574587135830579854380000000000000)
      constant := (155899071577084582394830312421333966301005555120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 83 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree083.table
  base := (911128294867348483075709462539885347011/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1426541891212765799101802605260000000000000)
      constant := (35810163833756651457831928299303935872492396) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 83 interval.damping) (curvature.centralUpper 83 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree083.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 83 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 83 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel083

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel084
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (44643650786596245343/10000000000000000000)
  centralHi := (446436507865962453431/100000000000000000000)
  directionLo := (22457521630353109331/5000000000000000000)
  directionHi := (449150432607062186621/100000000000000000000)

def endpointA : IntegerEndpointWitness 84 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree084.table
  base := (1420884505555438432094039043193264530189/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-2109646203593815896741858759236880000000000000)
      constant := (53207649167841070792871750763895594112332500024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 84 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree084.table
  base := (710441955999647783794963053495696754773/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-481036812173852343921254261760000000000000)
      constant := (12221832321631970792847854445803896722114552) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 84 interval.damping) (curvature.centralUpper 84 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree084.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 84 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 84 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel084

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel085
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (22457521630353109331/5000000000000000000)
  centralHi := (449150432607062186621/100000000000000000000)
  directionLo := (451848057057531969937/100000000000000000000)
  directionHi := (225924028528765984969/50000000000000000000)

def endpointA : IntegerEndpointWitness 85 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree085.table
  base := (48593706886034725233652223732451447519/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-6401582214220320793315321975566900000000000000)
      constant := (163390961707561881813646695261052863763000076480) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 85 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree085.table
  base := (1943747779519757360695106161542624738043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1459678981830348264425722965300000000000000)
      constant := (37530966977812621381150616496628034490569548) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 85 interval.damping) (curvature.centralUpper 85 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree085.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 85 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 85 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel085

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel086
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (451848057057531969937/100000000000000000000)
  centralHi := (225924028528765984969/50000000000000000000)
  directionLo := (90905934288630953429/20000000000000000000)
  directionHi := (227264835721577383573/50000000000000000000)

def endpointA : IntegerEndpointWitness 86 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree086.table
  base := (2479720266765289906961963587190578212233/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-6474225817659193896405067673423160000000000000)
      constant := (167203114181554864137470374412087392083499234184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 86 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree086.table
  base := (77491245389857889334398363072570409421/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1476247527139139497087683145320000000000000)
      constant := (38406573870888460335120229704669601111652992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 86 interval.damping) (curvature.centralUpper 86 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree086.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 86 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 86 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel086

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel087
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (90905934288630953429/20000000000000000000)
  centralHi := (227264835721577383573/50000000000000000000)
  directionLo := (45719555747817342257/10000000000000000000)
  directionHi := (457195557478173422571/100000000000000000000)

def endpointA : IntegerEndpointWitness 87 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree087.table
  base := (378600054637491701298512111733533128711/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-2182289807032688999831604457093140000000000000)
      constant := (57019801639584732283103858056533978688813939008) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 87 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree087.table
  base := (605760018210301596968149057201195375441/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-497605357482643576583214441780000000000000)
      constant := (13097439214230031272296274391549571722526460) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 87 interval.damping) (curvature.centralUpper 87 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree087.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 87 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 87 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel087

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel088
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (45719555747817342257/10000000000000000000)
  centralHi := (457195557478173422571/100000000000000000000)
  directionLo := (459845988710713158193/100000000000000000000)
  directionHi := (229922994355356579097/50000000000000000000)

def endpointA : IntegerEndpointWitness 88 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree088.table
  base := (3590988748749207275212973599445900774933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-6619513024536940102584559069135680000000000000)
      constant := (174959833913164388593492331852951791626451543784) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 88 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree088.table
  base := (3590988459739661630576873128520190764869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1509384617756721962411603505360000000000000)
      constant := (40188198291939224383349020769266726867535284) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 88 interval.damping) (curvature.centralUpper 88 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree088.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 88 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 88 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel088

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel089
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (459845988710713158193/100000000000000000000)
  centralHi := (229922994355356579097/50000000000000000000)
  directionLo := (462481230850386931557/100000000000000000000)
  directionHi := (231240615425193465779/50000000000000000000)

def endpointA : IntegerEndpointWitness 89 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree089.table
  base := (1041571291997748018617694379332788264943/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-6692156627975813205674304766991940000000000000)
      constant := (178904401159422003814821388329291821481850617056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 89 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree089.table
  base := (20831424633248855701847690603459139273/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1525953163065513195073563685380000000000000)
      constant := (41094215817487806913301397139617405802765600) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 89 interval.damping) (curvature.centralUpper 89 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree089.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 89 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 89 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel089

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel090
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (462481230850386931557/100000000000000000000)
  centralHi := (231240615425193465779/50000000000000000000)
  directionLo := (93020308415838838143/20000000000000000000)
  directionHi := (116275385519798547679/25000000000000000000)

def endpointA : IntegerEndpointWitness 90 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree090.table
  base := (2377344832224702287953248086848146432481/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-2254933410471562102921350154949400000000000000)
      constant := (60964368884231939668388482791561557662528825392) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 90 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree090.table
  base := (4754689462939644557933093253713639962101/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-514173902791434809245174621800000000000000)
      constant := (14003456739432507498773222997794563679545212) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 90 interval.damping) (curvature.centralUpper 90 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree090.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 90 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 90 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel090

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel091
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (93020308415838838143/20000000000000000000)
  centralHi := (116275385519798547679/25000000000000000000)
  directionLo := (467707173346742673197/100000000000000000000)
  directionHi := (233853586673371336599/50000000000000000000)

def endpointA : IntegerEndpointWitness 91 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree091.table
  base := (5356202210574004442019264692575725533353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-6837443834853559411853796162704460000000000000)
      constant := (186925950388603991729725674432337770244628727944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 91 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree091.table
  base := (5356202042342573095812215672427412171133/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1559090253683095660397484045420000000000000)
      constant := (42936661493422769616055444707779886838160788) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 91 interval.damping) (curvature.centralUpper 91 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree091.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 91 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 91 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel091

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel092
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (467707173346742673197/100000000000000000000)
  centralHi := (233853586673371336599/50000000000000000000)
  directionLo := (470298368650748729721/100000000000000000000)
  directionHi := (235149184325374364861/50000000000000000000)

def endpointA : IntegerEndpointWitness 92 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree092.table
  base := (746352847650934351121783472534993109089/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-6910087438292432514943541860560720000000000000)
      constant := (191002932363145301055942866799420384672115098176) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 92 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree092.table
  base := (5970822640775552702982567515283913434751/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1575658798991886893059444225440000000000000)
      constant := (43873089641996560126671848119790220883651036) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 92 interval.damping) (curvature.centralUpper 92 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree092.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 92 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 92 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel092

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel093
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (470298368650748729721/100000000000000000000)
  centralHi := (235149184325374364861/50000000000000000000)
  directionLo := (118218841325925895933/25000000000000000000)
  directionHi := (472875365303703583733/100000000000000000000)

def endpointA : IntegerEndpointWitness 93 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree093.table
  base := (1649637838306622432257774147535230656009/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-2327577013910435206011095852805660000000000000)
      constant := (65041350857547342746160269643229219903835892576) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 93 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree093.table
  base := (1649637809003538511236923524646870868271/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-530742448100226041907134801820000000000000)
      constant := (14939884887739604857375668953600549801677008) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 93 interval.damping) (curvature.centralUpper 93 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree093.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 93 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 93 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel093

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel094
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118218841325925895933/25000000000000000000)
  centralHi := (472875365303703583733/100000000000000000000)
  directionLo := (475438394186530403171/100000000000000000000)
  directionHi := (118859598546632600793/25000000000000000000)

def endpointA : IntegerEndpointWitness 94 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree094.table
  base := (7239387905243134113018209253568084285219/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 720000000000000000000000000000000000000000
      center := (1959)
      previous := (0)
      next := (1425)
      square := (28403220529356398849074594320000000000000)
      linear := (-3193922428777808384392500342360000000000000)
      constant := (90216980993070379428808033242201902068535768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 94 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree094.table
  base := (7239387807422454026252791547903679166687/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1608795889609469358383364585480000000000000)
      constant := (45776356556346639720984547991334532450000732) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 94 interval.damping) (curvature.centralUpper 94 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree094.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 94 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 94 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel094

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel095
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (475438394186530403171/100000000000000000000)
  centralHi := (118859598546632600793/25000000000000000000)
  directionLo := (477987679989999556287/100000000000000000000)
  directionHi := (7468557499843743067/1562500000000000000)

def endpointA : IntegerEndpointWitness 95 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree095.table
  base := (789333241735643241198019887001102200683/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-7128018248609051824212778954129500000000000000)
      constant := (203498707683131410456101016749710669278142297840) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 95 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree095.table
  base := (3946666167864233106507706481157917336689/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1625364434918260591045324765500000000000000)
      constant := (46743195320686244061624703422955870048241608) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 95 interval.damping) (curvature.centralUpper 95 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree095.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 95 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 95 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel095

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel096
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (477987679989999556287/100000000000000000000)
  centralHi := (7468557499843743067/1562500000000000000)
  directionLo := (480523441444616495389/100000000000000000000)
  directionHi := (48052344144461649539/10000000000000000000)

def endpointA : IntegerEndpointWitness 96 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree096.table
  base := (8560384870945352758340780995058578014043/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-2400220617349308309100841550661920000000000000)
      constant := (69250747525999072418532916664810985571992503688) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 96 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree096.table
  base := (342415392113487106291410711808804763523/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-547310993409017274569094981840000000000000)
      constant := (15906723651862069042640420898662641429056900) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 96 interval.damping) (curvature.centralUpper 96 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree096.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 96 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 96 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel096

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel097
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (480523441444616495389/100000000000000000000)
  centralHi := (48052344144461649539/10000000000000000000)
  directionLo := (483045891539647952457/100000000000000000000)
  directionHi := (241522945769823976229/50000000000000000000)

def endpointA : IntegerEndpointWitness 97 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree097.table
  base := (9240545248496149492874506962331575102477/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-7273305455486798030392270349842020000000000000)
      constant := (212049915695504362337121656006700588606898761896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 97 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree097.table
  base := (9240545191674677646118597425031132956951/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1658501525535843056369245125540000000000000)
      constant := (48707283460431868134208250500053620786450236) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 97 interval.damping) (curvature.centralUpper 97 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree097.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 97 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 97 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel097

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel098
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (483045891539647952457/100000000000000000000)
  centralHi := (241522945769823976229/50000000000000000000)
  directionLo := (485555237731907170587/100000000000000000000)
  directionHi := (121388809432976792647/25000000000000000000)

def endpointA : IntegerEndpointWitness 98 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree098.table
  base := (4966906766729071754949125929989953700923/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-7345949058925671133482016047698280000000000000)
      constant := (216391727033020493290269045135533629312448802608) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 98 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree098.table
  base := (19401979464957033033196920334182756739/19531250000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1675070070844634289031205305560000000000000)
      constant := (49704532834640640330890998004089656572213248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 98 interval.damping) (curvature.centralUpper 98 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree098.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 98 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 98 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel098

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel099
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (485555237731907170587/100000000000000000000)
  centralHi := (121388809432976792647/25000000000000000000)
  directionLo := (488051682144877402987/100000000000000000000)
  directionHi := (122012920536219350747/25000000000000000000)

def endpointA : IntegerEndpointWitness 99 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree099.table
  base := (10640189710123061756325649602823014401047/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-2472864220788181412190587248518180000000000000)
      constant := (73592558862682413567497879009272093681485907752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 99 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree099.table
  base := (1064018967058624602862146969280657615141/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-563879538717808507231055161860000000000000)
      constant := (16903973025886030422171586697171178913816920) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 99 interval.damping) (curvature.centralUpper 99 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree099.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 99 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 99 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel099

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel100
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (488051682144877402987/100000000000000000000)
  centralHi := (122012920536219350747/25000000000000000000)
  directionLo := (490535421758714586713/100000000000000000000)
  directionHi := (245267710879357293357/50000000000000000000)

def endpointA : IntegerEndpointWitness 100 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree100.table
  base := (5679836881761950892665118553097302356657/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-7491236265803417339661507443410800000000000000)
      constant := (225207764358204132768632576382858539490443165072) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 100 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree100.table
  base := (11359673730549303823031635100519484136353/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1708207161462216754355125665600000000000000)
      constant := (51729442188954657010960944298618701428908708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 100 interval.damping) (curvature.centralUpper 100 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree100.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 100 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 100 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel100

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel101
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (490535421758714586713/100000000000000000000)
  centralHi := (245267710879357293357/50000000000000000000)
  directionLo := (493006648591634670213/100000000000000000000)
  directionHi := (246503324295817335107/50000000000000000000)

def endpointA : IntegerEndpointWitness 101 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree101.table
  base := (483690627173999411407651918595643474133/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-7563879869242290442751253141267060000000000000)
      constant := (229681990341215084724563306697845583831847634600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 101 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree101.table
  base := (12092265651851169483733561769574746398323/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1724775706771007987017085845620000000000000)
      constant := (52757102168022881390979775349477190870339628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 101 interval.damping) (curvature.centralUpper 101 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree101.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 101 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 101 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel101

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel102
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (493006648591634670213/100000000000000000000)
  centralHi := (246503324295817335107/50000000000000000000)
  directionLo := (30966596867072393523/6250000000000000000)
  directionHi := (495465549873158296369/100000000000000000000)

def endpointA : IntegerEndpointWitness 102 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree102.table
  base := (64189827219377207117296506057458873749/50000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-2545507824227054515280332946374440000000000000)
      constant := (78066784844965674755375464990490362930135396800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 102 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree102.table
  base := (12837965420945339104459265312390108742933/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-580448084026599739893015341880000000000000)
      constant := (17931633004791696755315201935378681304915196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 102 interval.damping) (curvature.centralUpper 102 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree102.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 102 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 102 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel102

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel103
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30966596867072393523/6250000000000000000)
  centralHi := (495465549873158296369/100000000000000000000)
  directionLo := (497912308209655193563/100000000000000000000)
  directionHi := (124478077052413798391/25000000000000000000)

def endpointA : IntegerEndpointWitness 103 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree103.table
  base := (6798386521949418845936559734896111921377/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-7709167076120036648930744536979580000000000000)
      constant := (238762856937150289955747925416804489867742338192) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 103 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree103.table
  base := (6798386512390113230884745353051331055871/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1757912797388590452341006205660000000000000)
      constant := (54842832727541426531814622487772195836022712) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 103 interval.damping) (curvature.centralUpper 103 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree103.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 103 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 103 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel103

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel104
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (497912308209655193563/100000000000000000000)
  centralHi := (124478077052413798391/25000000000000000000)
  directionLo := (250173550871301252263/50000000000000000000)
  directionHi := (500347101742602504527/100000000000000000000)

def endpointA : IntegerEndpointWitness 104 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree104.table
  base := (14368688466692070082965942045666687279053/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-7781810679558909752020490234835840000000000000)
      constant := (243369497545950502307248316726566475278358821544) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 104 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree104.table
  base := (7184344225376447394411346824099478472151/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1774481342697381685002966385680000000000000)
      constant := (55900903307068184464980529799495162449994872) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 104 interval.damping) (curvature.centralUpper 104 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree104.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 104 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 104 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel104

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel105
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (250173550871301252263/50000000000000000000)
  centralHi := (500347101742602504527/100000000000000000000)
  directionLo := (4022160834399561623/800000000000000000)
  directionHi := (125692526074986300719/25000000000000000000)

def endpointA : IntegerEndpointWitness 105 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree105.table
  base := (757685584997847511608031804603010454347/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-2618151427665927618370078644230700000000000000)
      constant := (82673425453113886352539435025232882794953211040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 105 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree105.table
  base := (378842792166742364843300807350502724547/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-597016629335390972554975521900000000000000)
      constant := (18989703584172130894578467144965741307782560) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 105 interval.damping) (curvature.centralUpper 105 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree105.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 105 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 105 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel105

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel106
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4022160834399561623/800000000000000000)
  centralHi := (125692526074986300719/25000000000000000000)
  directionLo := (101036297108184508789/20000000000000000000)
  directionHi := (252590742770461271973/50000000000000000000)

def endpointA : IntegerEndpointWitness 106 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree106.table
  base := (15951842731788196483261738589860503969753/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-7927097886436655958199981630548360000000000000)
      constant := (252715193375430248970003314461937238435381275144) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 106 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree106.table
  base := (797592136035632155188244297232228853801/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1807618433314964150326886745720000000000000)
      constant := (58047455063460603808260863048817204774736720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 106 interval.damping) (curvature.centralUpper 106 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree106.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 106 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 106 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel106

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel107
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (101036297108184508789/20000000000000000000)
  centralHi := (252590742770461271973/50000000000000000000)
  directionLo := (507581411094702018037/100000000000000000000)
  directionHi := (253790705547351009019/50000000000000000000)

def endpointA : IntegerEndpointWitness 107 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree107.table
  base := (16763081550641758484241796064640597680423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-7999741489875529061289727328404620000000000000)
      constant := (257454248592380213924014082465081584029875917304) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 107 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree107.table
  base := (4190770385352645689098821444768895929057/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1824186978623755382988846925740000000000000)
      constant := (59135936239487856166305979763699221013784208) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 107 interval.damping) (curvature.centralUpper 107 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree107.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 107 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 107 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel107

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel108
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (507581411094702018037/100000000000000000000)
  centralHi := (253790705547351009019/50000000000000000000)
  directionLo := (509970042693141382571/100000000000000000000)
  directionHi := (127492510673285345643/25000000000000000000)

def endpointA : IntegerEndpointWitness 108 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree108.table
  base := (4396857036326897248822772183838244258121/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-2690795031104800721459824342086960000000000000)
      constant := (87412480669469539442084450924465213430354171744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 108 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree108.table
  base := (1758742813761432277045885804415422259/1000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-613585174644182205216935701920000000000000)
      constant := (20078184760065592963249611374809850671080000) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 108 interval.damping) (curvature.centralUpper 108 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree108.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 108 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 108 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel108

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel109
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (509970042693141382571/100000000000000000000)
  centralHi := (127492510673285345643/25000000000000000000)
  directionLo := (512347538297979919161/100000000000000000000)
  directionHi := (256173769148989959581/50000000000000000000)

def endpointA : IntegerEndpointWitness 109 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree109.table
  base := (18424882504886128786722810722663680047781/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-8145028696753275267469218724117140000000000000)
      constant := (267064773621781909080357898285383099234239472488) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 109 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree109.table
  base := (18424882498475105375502715853136710588153/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1857324069241337848312767285780000000000000)
      constant := (61343309185196816698853122203085421581173508) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 109 interval.damping) (curvature.centralUpper 109 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree109.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 109 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 109 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel109

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel110
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (512347538297979919161/100000000000000000000)
  centralHi := (256173769148989959581/50000000000000000000)
  directionLo := (128678513055685494357/25000000000000000000)
  directionHi := (514714052222741977429/100000000000000000000)

def endpointA : IntegerEndpointWitness 110 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree110.table
  base := (3855088923753579270500340858303994275949/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-8217672300192148370558964421973400000000000000)
      constant := (271936243430812669371755823328799293408005682760) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 110 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree110.table
  base := (3855088922685170367425408256181097143873/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1873892614550129080974727465800000000000000)
      constant := (62462200954107554759180450554362597485897140) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 110 interval.damping) (curvature.centralUpper 110 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree110.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 110 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 110 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel110

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel111
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (128678513055685494357/25000000000000000000)
  centralHi := (514714052222741977429/100000000000000000000)
  directionLo := (258534867624809512419/50000000000000000000)
  directionHi := (517069735249619024839/100000000000000000000)

def endpointA : IntegerEndpointWitness 111 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree111.table
  base := (20139114476615678237369829372947123158423/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-2763438634543673824549570039943220000000000000)
      constant := (92283950477952262024938421017184643431366953768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 111 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree111.table
  base := (1258694654510296073985114103824178594601/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-630153719952973437878895881940000000000000)
      constant := (21197076528852709123918099622091742290163392) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 111 interval.damping) (curvature.centralUpper 111 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree111.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 111 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 111 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel111

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel112
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (258534867624809512419/50000000000000000000)
  centralHi := (517069735249619024839/100000000000000000000)
  directionLo := (259707367370790362541/50000000000000000000)
  directionHi := (519414734741580725083/100000000000000000000)

def endpointA : IntegerEndpointWitness 112 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree112.table
  base := (10507946034174450924746655116014341515331/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-8362959507069894576738455817685920000000000000)
      constant := (281811597629310964279950223185760017978660729776) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 112 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree112.table
  base := (1313493254040044998460600743926881724359/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1907029705167711546298647825840000000000000)
      constant := (64730395082186697044733318683541883873230784) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 112 interval.damping) (curvature.centralUpper 112 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree112.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 112 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 112 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel112

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel113
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (259707367370790362541/50000000000000000000)
  centralHi := (519414734741580725083/100000000000000000000)
  directionLo := (260874597374975464581/50000000000000000000)
  directionHi := (521749194749950929163/100000000000000000000)

def endpointA : IntegerEndpointWitness 113 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree113.table
  base := (21905777384129843828107643547752551584461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-8435603110508767679828201515542180000000000000)
      constant := (286815482015610533762077831007217224074405353128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 113 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree113.table
  base := (10952888690520358705643318155294938027319/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1923598250476502778960608005860000000000000)
      constant := (65879697440639992797293614513133735537966968) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 113 interval.damping) (curvature.centralUpper 113 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree113.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 113 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 113 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel113

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel114
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (260874597374975464581/50000000000000000000)
  centralHi := (521749194749950929163/100000000000000000000)
  directionLo := (524073256117670803033/100000000000000000000)
  directionHi := (262036628058835401517/50000000000000000000)

def endpointA : IntegerEndpointWitness 114 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree114.table
  base := (22808770414351385936637131690906839533479/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-2836082237982546927639315737799480000000000000)
      constant := (97287834863742500526635731653131552004706922664) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 114 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree114.table
  base := (11404385205889084453870798411840843450061/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-646722265261764670540856061960000000000000)
      constant := (22346378887190966149473139826954180242801464) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 114 interval.damping) (curvature.centralUpper 114 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree114.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 114 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 114 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel114

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel115
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (524073256117670803033/100000000000000000000)
  centralHi := (262036628058835401517/50000000000000000000)
  directionLo := (526387056578458560157/100000000000000000000)
  directionHi := (263193528289229280079/50000000000000000000)

def endpointA : IntegerEndpointWitness 115 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree115.table
  base := (5931217787406519797055278199596043442473/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-8580890317386513886007692911254700000000000000)
      constant := (296955665354668812746976100494288812319753782816) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 115 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree115.table
  base := (23724871147482774928557413685415339838551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1956735341094085244284528365900000000000000)
      constant := (68208712744648083214808358715487452234187836) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 115 interval.damping) (curvature.centralUpper 115 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree115.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 115 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 115 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel115

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel116
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (526387056578458560157/100000000000000000000)
  centralHi := (263193528289229280079/50000000000000000000)
  directionLo := (264345365426031674587/50000000000000000000)
  directionHi := (21147629234082533967/4000000000000000000)

def endpointA : IntegerEndpointWitness 116 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree116.table
  base := (12327039790388158622197785995321220108039/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-8653533920825386989097438609110960000000000000)
      constant := (302091964304474787330364522973338278831486773744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 116 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree116.table
  base := (12327039789495616964151282583667372134177/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-1973303886402876476946488545920000000000000)
      constant := (69388425689535668240824897434784050793660744) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 116 interval.damping) (curvature.centralUpper 116 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree116.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 116 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 116 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel116

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel117
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (264345365426031674587/50000000000000000000)
  centralHi := (21147629234082533967/4000000000000000000)
  directionLo := (530984410735799704461/100000000000000000000)
  directionHi := (265492205367899852231/50000000000000000000)

def endpointA : IntegerEndpointWitness 117 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree117.table
  base := (25596395698825453514958251592315237801869/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-2908725841421420030729061435655740000000000000)
      constant := (102424133813072569214397991239263793397303886904) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 117 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree117.table
  base := (25596395697338830088513567809835903667809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-663290810570555903202816241980000000000000)
      constant := (23526091831970974585668116744735530844013708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 117 interval.damping) (curvature.centralUpper 117 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree117.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 117 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 117 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel117

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel118
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (530984410735799704461/100000000000000000000)
  centralHi := (265492205367899852231/50000000000000000000)
  directionLo := (133317056298134635943/25000000000000000000)
  directionHi := (533268225192538543773/100000000000000000000)

def endpointA : IntegerEndpointWitness 118 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree118.table
  base := (26551819494989724031156751380472118577601/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-8798821127703133195276930004823480000000000000)
      constant := (312496976757500533593762320976991474515530283848) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 118 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree118.table
  base := (6637954873437937296503500375676530222327/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2006440977020458942270408905960000000000000)
      constant := (71778262163463992451312365989787420352015088) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 118 interval.damping) (curvature.centralUpper 118 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree118.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 118 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 118 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel118

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel119
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (133317056298134635943/25000000000000000000)
  centralHi := (533268225192538543773/100000000000000000000)
  directionLo := (535542300435320940443/100000000000000000000)
  directionHi := (133885575108830235111/25000000000000000000)

def endpointA : IntegerEndpointWitness 119 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree119.table
  base := (27520350960670861059841107039620154595937/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-8871464731142006298366675702679740000000000000)
      constant := (317765690257955727895647529226488042598174587976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 119 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree119.table
  base := (5504070191928004065687831133003054087053/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2023009522329250174932369085980000000000000)
      constant := (72988385691879635371623815120613049735669540) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 119 interval.damping) (curvature.centralUpper 119 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree119.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 119 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 119 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel119

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel120
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (535542300435320940443/100000000000000000000)
  centralHi := (133885575108830235111/25000000000000000000)
  directionLo := (2151227040035007039/400000000000000000)
  directionHi := (537806760008751759751/100000000000000000000)

def endpointA : IntegerEndpointWitness 120 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree120.table
  base := (14250995043724650697541164982494054876591/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-2981369444860293133818807133512000000000000000)
      constant := (107692847313081391953357668228889809626674696912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 120 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree120.table
  base := (28501990086590998168994182653288352298619/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-679859355879347135864776422000000000000000)
      constant := (24736215360285665761818027703839460227583428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 120 interval.damping) (curvature.centralUpper 120 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree120.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 120 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 120 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel120

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel121
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (2151227040035007039/400000000000000000)
  centralHi := (537806760008751759751/100000000000000000000)
  directionLo := (540061724867321685913/100000000000000000000)
  directionHi := (270030862433660842957/50000000000000000000)

def endpointA : IntegerEndpointWitness 121 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree121.table
  base := (5899347373415581797070890347557606951613/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-9016751938019752504546167098392260000000000000)
      constant := (328435531800054186992315645132464247602200722120) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 121 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree121.table
  base := (29496736866363314183493555528053072101567/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2056146612946832640256289446020000000000000)
      constant := (75439043330099388925932490992682410595656412) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 121 interval.damping) (curvature.centralUpper 121 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree121.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 121 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 121 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel121

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel122
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (540061724867321685913/100000000000000000000)
  centralHi := (270030862433660842957/50000000000000000000)
  directionLo := (108461462690159627447/20000000000000000000)
  directionHi := (135576828362699534309/25000000000000000000)

def endpointA : IntegerEndpointWitness 122 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree122.table
  base := (3813073911434518073778181944245532775231/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-9089395541458625607635912796248520000000000000)
      constant := (333836659839100567687263219155221052974679520704) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 122 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree122.table
  base := (6100918258176247432784282133886087156069/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2072715158255623872918249626040000000000000)
      constant := (76679577439316083969570467673789495688092420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 122 interval.damping) (curvature.centralUpper 122 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree122.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 122 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 122 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel122

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel123
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (108461462690159627447/20000000000000000000)
  centralHi := (135576828362699534309/25000000000000000000)
  directionLo := (544543641756818034539/100000000000000000000)
  directionHi := (27227182087840901727/5000000000000000000)

def endpointA : IntegerEndpointWitness 123 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree123.table
  base := (15762776676362312987369531402828870811241/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-3054013048299166236908552831368260000000000000)
      constant := (113093975351707918679736800184972359579857505712) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 123 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree123.table
  base := (6305110670445878534353034584745264183657/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-696427901188138368526736602020000000000000)
      constant := (25976749469407376312193853483102215851019420) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 123 interval.damping) (curvature.centralUpper 123 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree123.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 123 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 123 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel123

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel124
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (544543641756818034539/100000000000000000000)
  centralHi := (27227182087840901727/5000000000000000000)
  directionLo := (136692705852702079479/25000000000000000000)
  directionHi := (546770823410808317917/100000000000000000000)

def endpointA : IntegerEndpointWitness 124 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree124.table
  base := (32559623043060031125950551434106516061207/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-9234682748336371813815404191961040000000000000)
      constant := (344771330446889011208642357177550353166502850936) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 124 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree124.table
  base := (32559623042647799145895928661364827967649/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2105852248873206338242169986080000000000000)
      constant := (79191056236538164490765128428569133806835364) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 124 interval.damping) (curvature.centralUpper 124 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree124.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 124 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 124 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel124

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel125
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (136692705852702079479/25000000000000000000)
  centralHi := (546770823410808317917/100000000000000000000)
  directionLo := (137247242433338366711/25000000000000000000)
  directionHi := (109797793946670693369/20000000000000000000)

def endpointA : IntegerEndpointWitness 125 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree125.table
  base := (16803400177435152215769935191774971966917/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-9307326351775244916905149889817300000000000000)
      constant := (350304873013185650974530809542804257732788430032) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 125 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree125.table
  base := (4200850044315898119784280499777340765421/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2122420794181997570904130166100000000000000)
      constant := (80462000923990256853511751991748374140441248) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 125 interval.damping) (curvature.centralUpper 125 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree125.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 125 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 125 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel125

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel126
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (137247242433338366711/25000000000000000000)
  centralHi := (109797793946670693369/20000000000000000000)
  directionLo := (551198189805123039687/100000000000000000000)
  directionHi := (68899773725640379961/12500000000000000000)

def endpointA : IntegerEndpointWitness 126 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree126.table
  base := (1386683411227605278290098060676674036199/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-3126656651738039339998298529224520000000000000)
      constant := (118627517917608777362086812365871298767578154600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 126 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree126.table
  base := (6933417056080911238214758333238578647103/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-712996446496929601188696782040000000000000)
      constant := (27247694156769912747926561119064314718826180) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 126 interval.damping) (curvature.centralUpper 126 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree126.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 126 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 126 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel126

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel127
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (551198189805123039687/100000000000000000000)
  centralHi := (68899773725640379961/12500000000000000000)
  directionLo := (553398590529466383099/100000000000000000000)
  directionHi := (5533985905294663831/1000000000000000000)

def endpointA : IntegerEndpointWitness 127 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree127.table
  base := (3574047781319665711485264368683175003289/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-9452613558652991123084641285529820000000000000)
      constant := (361504372664646368849185535998291492429231088720) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 127 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree127.table
  base := (2233779863309936841547167382350435576581/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2155557884799580036228050526140000000000000)
      constant := (83034300875233055419905486357186350892110656) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 127 interval.damping) (curvature.centralUpper 127 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree127.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 127 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 127 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel127

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel128
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (553398590529466383099/100000000000000000000)
  centralHi := (5533985905294663831/1000000000000000000)
  directionLo := (4444722213542209159/800000000000000000)
  directionHi := (138897569173194036219/25000000000000000000)

def endpointA : IntegerEndpointWitness 128 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree128.table
  base := (9206744486301353076133021051456928657627/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-9525257162091864226174386983386080000000000000)
      constant := (367170329747503086060491785776120806356553036384) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 128 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree128.table
  base := (18413488972503813969100262330247339836641/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2172126430108371268890010706160000000000000)
      constant := (84335656138501625535608971358817808468238152) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 128 interval.damping) (curvature.centralUpper 128 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree128.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 128 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 128 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel128

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel129
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (4444722213542209159/800000000000000000)
  centralHi := (138897569173194036219/25000000000000000000)
  directionLo := (111554670204543406397/20000000000000000000)
  directionHi := (278886675511358515993/50000000000000000000)

def endpointA : IntegerEndpointWitness 129 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree129.table
  base := (379265856696664456934720132175074780373/100000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-3199300255176912443088044227080780000000000000)
      constant := (124293475000091734327024342771153855205625496800) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 129 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree129.table
  base := (37926585669501861761358239142369668456229/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-729564991805720833850656962060000000000000)
      constant := (28549049419953899545429409014865936021474748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 129 interval.damping) (curvature.centralUpper 129 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree129.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 129 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 129 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel129

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel130
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (111554670204543406397/20000000000000000000)
  centralHi := (278886675511358515993/50000000000000000000)
  directionLo := (279973957122205683673/50000000000000000000)
  directionHi := (559947914244411367347/100000000000000000000)

def endpointA : IntegerEndpointWitness 130 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree130.table
  base := (39039300979660625278050013088220023552381/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-9670544368969610432353878379098600000000000000)
      constant := (378634658421862245504017125330516843305959093288) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 130 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree130.table
  base := (1219978155610114903030104340697640991091/312500000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2205263520725953734213931066200000000000000)
      constant := (86968777239064226216601732038733682421736832) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 130 interval.damping) (curvature.centralUpper 130 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree130.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 130 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 130 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel130

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel131
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (279973957122205683673/50000000000000000000)
  centralHi := (559947914244411367347/100000000000000000000)
  directionLo := (562114065134668394397/100000000000000000000)
  directionHi := (281057032567334197199/50000000000000000000)

def endpointA : IntegerEndpointWitness 131 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree131.table
  base := (40165123868396104872350040158268942608717/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-9743187972408483535443624076954860000000000000)
      constant := (384433030011183984077146501915299245034031221416) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 131 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree131.table
  base := (1606604954731286337238914098056541064509/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2221832066034744966875891246220000000000000)
      constant := (88300543075864735339643939367623386958058100) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 131 interval.damping) (curvature.centralUpper 131 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree131.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 131 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 131 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel131

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel132
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (562114065134668394397/100000000000000000000)
  centralHi := (281057032567334197199/50000000000000000000)
  directionLo := (282135950287169969587/50000000000000000000)
  directionHi := (22570876022973597567/4000000000000000000)

def endpointA : IntegerEndpointWitness 132 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree132.table
  base := (41304054329204938753994994038844763508939/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-3271943858615785546177789924937040000000000000)
      constant := (130091846589059965089736175001723133982189910024) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 132 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree132.table
  base := (20652027164555068167824489878729036034533/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-746133537114512066512617142080000000000000)
      constant := (29880815256674402628138762743369496864828792) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 132 interval.damping) (curvature.centralUpper 132 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree132.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 132 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 132 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel132

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel133
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (282135950287169969587/50000000000000000000)
  centralHi := (22570876022973597567/4000000000000000000)
  directionLo := (113284303119776189641/20000000000000000000)
  directionHi := (283210757799440474103/50000000000000000000)

def endpointA : IntegerEndpointWitness 133 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree133.table
  base := (1061402308888495836230369447807572955939/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-9888475179286229741623115472667380000000000000)
      constant := (396162187688808645147787008241474580789847442880) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 133 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree133.table
  base := (5307011544432620399536511738577753386309/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2254969156652327432199811606260000000000000)
      constant := (90994485321303964543989592057362892975256992) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 133 interval.damping) (curvature.centralUpper 133 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree133.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 133 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 133 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel133

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel134
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (113284303119776189641/20000000000000000000)
  centralHi := (283210757799440474103/50000000000000000000)
  directionLo := (35535187715449347577/6250000000000000000)
  directionHi := (568563003447189561233/100000000000000000000)

def endpointA : IntegerEndpointWitness 134 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree134.table
  base := (43621237940971026609857951541121681037483/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-9961118782725102844712861170523640000000000000)
      constant := (402092973775047592870933161357317426125649596184) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 134 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree134.table
  base := (43621237940905414713179476748107536986493/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2271537701961118664861771786280000000000000)
      constant := (92356661729475553243573832995741871331513748) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 134 interval.damping) (curvature.centralUpper 134 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree134.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 134 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 134 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel134

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel135
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (35535187715449347577/6250000000000000000)
  centralHi := (568563003447189561233/100000000000000000000)
  directionLo := (570696455608797735631/100000000000000000000)
  directionHi := (35668528475549858477/6250000000000000000)

def endpointA : IntegerEndpointWitness 135 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree135.table
  base := (44799491079183284173216143755306626955547/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-3344587462054658649267535622793300000000000000)
      constant := (136022632674964104363813781111617554884675279752) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 135 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree135.table
  base := (44799491079128704886270330683421072658327/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-762702082423303299174577322100000000000000)
      constant := (31242991664770213895722514110638552871899924) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 135 interval.damping) (curvature.centralUpper 135 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree135.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 135 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 135 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel135

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel136
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (570696455608797735631/100000000000000000000)
  centralHi := (35668528475549858477/6250000000000000000)
  directionLo := (572821961869480000823/100000000000000000000)
  directionHi := (71602745233685000103/12500000000000000000)

def endpointA : IntegerEndpointWitness 136 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree136.table
  base := (11497712940993252010089588006581689644361/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-10106405989602849050892352566236160000000000000)
      constant := (414086960437356135938872776083922498298225313312) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 136 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree136.table
  base := (22995425881963804358186086134403528685113/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2304674792578701130185692146320000000000000)
      constant := (95111425115585913774799790661837054065328136) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 136 interval.damping) (curvature.centralUpper 136 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree136.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 136 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 136 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel136

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel137
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (572821961869480000823/100000000000000000000)
  centralHi := (71602745233685000103/12500000000000000000)
  directionLo := (574939610355344673007/100000000000000000000)
  directionHi := (35933725647209042063/6250000000000000000)

def endpointA : IntegerEndpointWitness 137 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree137.table
  base := (47195319989245447392681045398360760595391/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-10179049593041722153982098264092420000000000000)
      constant := (420150161011469703485030205213065458501175747768) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 137 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree137.table
  base := (47195319989207686041382066379051616817623/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2321243337887492362847652326340000000000000)
      constant := (96504012093081969660634872320998358205434428) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 137 interval.damping) (curvature.centralUpper 137 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree137.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 137 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 137 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel137

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel138
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (574939610355344673007/100000000000000000000)
  centralHi := (35933725647209042063/6250000000000000000)
  directionLo := (72131185946933598931/12500000000000000000)
  directionHi := (577049487575468791449/100000000000000000000)

def endpointA : IntegerEndpointWitness 138 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree138.table
  base := (3025805984313250469782171523733990586483/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-3417231065493531752357281320649560000000000000)
      constant := (142085833248760180572631309116030414918927723648) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 138 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree138.table
  base := (24206447874490300396817919289215786180663/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-779270627732094531836537502120000000000000)
      constant := (32635578642194409748745625676571178868335912) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 138 interval.damping) (curvature.centralUpper 138 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree138.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 138 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 138 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel138

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel139
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72131185946933598931/12500000000000000000)
  centralHi := (577049487575468791449/100000000000000000000)
  directionLo := (289575839231567568061/50000000000000000000)
  directionHi := (579151678463135136123/100000000000000000000)

def endpointA : IntegerEndpointWitness 139 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree139.table
  base := (24821789518693825322093788364008590925759/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-10324336799919468360161589659804940000000000000)
      constant := (432408976640852647150591266552581262989120234864) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 139 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree139.table
  base := (12410894759340382633480123192999755402033/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2354380428505074828171572686380000000000000)
      constant := (99319596615877838923794136928564464777892752) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 139 interval.damping) (curvature.centralUpper 139 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree139.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 139 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 139 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel139

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel140
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (289575839231567568061/50000000000000000000)
  centralHi := (579151678463135136123/100000000000000000000)
  directionLo := (72655783301965867817/12500000000000000000)
  directionHi := (581246266415726942537/100000000000000000000)

def endpointA : IntegerEndpointWitness 140 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree140.table
  base := (1272184246214709596635577977293208965433/250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-10396980403358341463251335357661200000000000000)
      constant := (438604591694266087278728578245333711981367511360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 140 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree140.table
  base := (25443684924283330802783248772585185948741/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2370948973813866060833532866400000000000000)
      constant := (100742594160757581401666548886626133388309352) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 140 interval.damping) (curvature.centralUpper 140 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree140.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 140 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 140 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel140

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel141
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (72655783301965867817/12500000000000000000)
  centralHi := (581246266415726942537/100000000000000000000)
  directionLo := (583333333333333333333/100000000000000000000)
  directionHi := (291666666666666666667/50000000000000000000)

def endpointA : IntegerEndpointWitness 141 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree141.table
  base := (52144268176928829630660087380873661254581/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 240000000000000000000000000000000000000000
      center := (653)
      previous := (0)
      next := (475)
      square := (9467740176452132949691531440000000000000)
      linear := (-1579843670861206362809880949980000000000000)
      constant := (67126051743717611916976496048649717870109944) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 141 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree141.table
  base := (52144268176910765671669421541720445870111/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-795839173040885764498497682140000000000000)
      constant := (34058576187005929486575184458358145350441332) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 141 interval.damping) (curvature.centralUpper 141 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree141.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 141 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 141 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel141

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel142
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (583333333333333333333/100000000000000000000)
  centralHi := (291666666666666666667/50000000000000000000)
  directionLo := (585412959656116028943/100000000000000000000)
  directionHi := (36588309978507251809/6250000000000000000)

def endpointA : IntegerEndpointWitness 142 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree142.table
  base := (10682854803363974954106675431126282098523/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-10542267610236087669430826753373720000000000000)
      constant := (451128236274015290564454068628840409576029430520) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 142 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree142.table
  base := (26707137008402426880514153657529948475977/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2404086064431448526157453226440000000000000)
      constant := (103618999816457256495007915925832156290270344) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 142 interval.damping) (curvature.centralUpper 142 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree142.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 142 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 142 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel142

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel143
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (585412959656116028943/100000000000000000000)
  centralHi := (36588309978507251809/6250000000000000000)
  directionLo := (293742612200242786331/50000000000000000000)
  directionHi := (587485224400485572663/100000000000000000000)

def endpointA : IntegerEndpointWitness 143 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree143.table
  base := (13674346840691598575971823495466430433661/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-10614911213674960772520572451229980000000000000)
      constant := (457456265798588127812678215300289455560451658912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 143 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree143.table
  base := (2734869368137695213152673480193644206289/500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2420654609740239758819413406460000000000000)
      constant := (105072407926878164729532407869491923828528080) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 143 interval.damping) (curvature.centralUpper 143 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree143.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 143 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 143 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel143

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel144
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (293742612200242786331/50000000000000000000)
  centralHi := (587485224400485572663/100000000000000000000)
  directionLo := (294775102597066550679/50000000000000000000)
  directionHi := (589550205194133101359/100000000000000000000)

def endpointA : IntegerEndpointWitness 144 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree144.table
  base := (27996804104682523304526894712977375082691/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-3562518272371277958536772716362080000000000000)
      constant := (154609477826158578413410873187159377034767892112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 144 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree144.table
  base := (6999201026169332698292690843557954730031/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-812407718349676997160457862160000000000000)
      constant := (35511984297361998654002835822101563654082976) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 144 interval.damping) (curvature.centralUpper 144 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree144.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 144 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 144 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel144

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel145
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (294775102597066550679/50000000000000000000)
  centralHi := (589550205194133101359/100000000000000000000)
  directionLo := (18487749322186300133/3125000000000000000)
  directionHi := (591607978309961604257/100000000000000000000)

def endpointA : IntegerEndpointWitness 145 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree145.table
  base := (7162867068912767099623737591289746282419/1250000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-10760198420552706978700063846942500000000000000)
      constant := (470244739312832980302404776271738768783809416896) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 145 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree145.table
  base := (5730293655129350243619146514998745813039/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2453791700357822224143333766500000000000000)
      constant := (108009634711889459753826978226712048492694040) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 145 interval.damping) (curvature.centralUpper 145 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree145.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 145 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 145 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel145

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel146
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (18487749322186300133/3125000000000000000)
  centralHi := (591607978309961604257/100000000000000000000)
  directionLo := (118731723739791726407/20000000000000000000)
  directionHi := (148414654674739658009/25000000000000000000)

def endpointA : IntegerEndpointWitness 146 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree146.table
  base := (14656343095837886339065269400067026103703/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-10832842023991580081789809544798760000000000000)
      constant := (476705183300828659143140043075801946470967018976) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 146 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree146.table
  base := (58625372383344366878307696907814349397919/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2470360245666613456805293946520000000000000)
      constant := (109493453386100417947353178986291316578325084) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 146 interval.damping) (curvature.centralUpper 146 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree146.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 146 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 146 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel146

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel147
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (118731723739791726407/20000000000000000000)
  centralHi := (148414654674739658009/25000000000000000000)
  directionLo := (297851100011025270307/50000000000000000000)
  directionHi := (119140440004410108123/20000000000000000000)

def endpointA : IntegerEndpointWitness 147 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree147.table
  base := (59960915700372719343820363684022664869057/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-3635161875810151061626518414218340000000000000)
      constant := (161069921813881725699317562553276454350697925912) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 147 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree147.table
  base := (2398436628014670061748166347815442005161/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-828976263658468229822418042180000000000000)
      constant := (36995802971511270807101203821762132601548300) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 147 interval.damping) (curvature.centralUpper 147 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree147.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 147 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 147 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel147

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel148
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (297851100011025270307/50000000000000000000)
  centralHi := (119140440004410108123/20000000000000000000)
  directionLo := (298869397340488286177/50000000000000000000)
  directionHi := (119547758936195314471/20000000000000000000)

def endpointA : IntegerEndpointWitness 148 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree148.table
  base := (15327391624327180894058403902478769226089/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-10978129230869326287969300940511280000000000000)
      constant := (489758485734478238739787876388844193151484013088) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 148 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree148.table
  base := (61309566497303762497019369631192911470863/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2503497336284195922129214306560000000000000)
      constant := (112491501297007594994005262351962944812951068) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 148 interval.damping) (curvature.centralUpper 148 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree148.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 148 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 148 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel148

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel149
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (298869397340488286177/50000000000000000000)
  centralHi := (119547758936195314471/20000000000000000000)
  directionLo := (74971059231027423321/12500000000000000000)
  directionHi := (599768473848219386569/100000000000000000000)

def endpointA : IntegerEndpointWitness 149 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree149.table
  base := (62671324769184349436937861878756534508953/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-11050772834308199391059046638367540000000000000)
      constant := (496351344178536547088598501771843455550579956744) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 149 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree149.table
  base := (62671324769180225440129779979916532772569/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2520065881592987154791174486580000000000000)
      constant := (114005730533342659390725683855849495179812484) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 149 interval.damping) (curvature.centralUpper 149 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree149.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 149 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 149 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel149

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel150
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (74971059231027423321/12500000000000000000)
  centralHi := (599768473848219386569/100000000000000000000)
  directionLo := (60179130749602704591/10000000000000000000)
  directionHi := (601791307496027045911/100000000000000000000)

def endpointA : IntegerEndpointWitness 150 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree150.table
  base := (32023095255552139529597268110971229570627/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-3707805479249024164716264112074600000000000000)
      constant := (167662780257680503876105176106979376413832722064) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 150 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree150.table
  base := (32023095255550425528818214367781267844607/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-845544808967259462484378222200000000000000)
      constant := (38510032207787591732036837793576750428270568) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 150 interval.damping) (curvature.centralUpper 150 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree150.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 150 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 150 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel150

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel151
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (60179130749602704591/10000000000000000000)
  centralHi := (601791307496027045911/100000000000000000000)
  directionLo := (603807364424559940571/100000000000000000000)
  directionHi := (150951841106139985143/25000000000000000000)

def endpointA : IntegerEndpointWitness 151 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree151.table
  base := (65434163718251302774044590765085322301199/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-11196060041185945597238538034080060000000000000)
      constant := (509669475517226964795510357389802626591361098552) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 151 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree151.table
  base := (32717081859124226716310054258382576142237/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2553202972210569620115094846620000000000000)
      constant := (117064599566894523717150659460876045482241064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 151 interval.damping) (curvature.centralUpper 151 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree151.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 151 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 151 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel151

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel152
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (603807364424559940571/100000000000000000000)
  centralHi := (150951841106139985143/25000000000000000000)
  directionLo := (151454178072298670923/25000000000000000000)
  directionHi := (605816712289194683693/100000000000000000000)

def endpointA : IntegerEndpointWitness 152 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree152.table
  base := (13367048877176917565964451039476948298039/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-11268703644624818700328283731936320000000000000)
      constant := (516394748410338886622696051542044768364532534360) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 152 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree152.table
  base := (6683524438588221957178748064614286985527/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2569771517519360852777055026640000000000000)
      constant := (118609239363767235686087561903901143314789720) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 152 interval.damping) (curvature.centralUpper 152 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree152.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 152 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 152 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel152

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel153
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (151454178072298670923/25000000000000000000)
  centralHi := (605816712289194683693/100000000000000000000)
  directionLo := (607819417627015634687/100000000000000000000)
  directionHi := (2374294600105529823/390625000000000000)

def endpointA : IntegerEndpointWitness 153 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree153.table
  base := (68249432509337996496338230335055226027897/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-3780449082687897267806009809930860000000000000)
      constant := (174388053150545045745387154373693946613094987352) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 153 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree153.table
  base := (68249432509336028180248316650587700181719/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-862113354276050695146338402220000000000000)
      constant := (40054672004604310245435057494924552402180628) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 153 interval.damping) (curvature.centralUpper 153 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree153.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 153 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 153 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel153

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel154
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (607819417627015634687/100000000000000000000)
  centralHi := (2374294600105529823/390625000000000000)
  directionLo := (609815545882523398301/100000000000000000000)
  directionHi := (304907772941261699151/50000000000000000000)

def endpointA : IntegerEndpointWitness 154 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree154.table
  base := (13935345616803690352827198044940501383921/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-11413990851502564906507775127648840000000000000)
      constant := (529977708640385196923706550587078389320549336040) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 154 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree154.table
  base := (69676728084016815918926365935068368764311/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2602908608136943318100975386680000000000000)
      constant := (121728929516866258587596746182072461275515196) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 154 interval.damping) (curvature.centralUpper 154 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree154.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 154 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 154 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel154

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel155
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (609815545882523398301/100000000000000000000)
  centralHi := (304907772941261699151/50000000000000000000)
  directionLo := (611805161432588402411/100000000000000000000)
  directionHi := (152951290358147100603/25000000000000000000)

def endpointA : IntegerEndpointWitness 155 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree155.table
  base := (17779282776351087234614103926934045903793/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-11486634454941438009597520825505100000000000000)
      constant := (536835395975869913501839265556098930781625876256) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 155 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree155.table
  base := (71117131105402989463062483868697655292603/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2619477153445734550762935566700000000000000)
      constant := (123303979872764441880270953789085615590533708) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 155 interval.damping) (curvature.centralUpper 155 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree155.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 155 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 155 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel155

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel156
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (611805161432588402411/100000000000000000000)
  centralHi := (152951290358147100603/25000000000000000000)
  directionLo := (613788327610676473273/100000000000000000000)
  directionHi := (306894163805338236637/50000000000000000000)

def endpointA : IntegerEndpointWitness 156 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree156.table
  base := (2902825662761760460389169698373812743769/400000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-3853092686126770370895755507787120000000000000)
      constant := (181245740485793752241688492209270311410591432600) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 156 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree156.table
  base := (14514128313808576351861208965934048991461/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-878681899584841927808298582240000000000000)
      constant := (41629722360449073533469057594476042939487660) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 156 interval.damping) (curvature.centralUpper 156 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree156.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 156 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 156 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel156

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel157
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (613788327610676473273/100000000000000000000)
  centralHi := (306894163805338236637/50000000000000000000)
  directionLo := (30788255336518609993/5000000000000000000)
  directionHi := (615765106730372199861/100000000000000000000)

def endpointA : IntegerEndpointWitness 157 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree157.table
  base := (74037259470554189758405251009641768136927/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-11631921661819184215777012221217620000000000000)
      constant := (550683185084222079491990319543967630188641965496) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 157 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree157.table
  base := (18509314867638312738066256007201595722689/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2652614244063317016086855926740000000000000)
      constant := (126484491142456798041211290272689529784067216) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 157 interval.damping) (curvature.centralUpper 157 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree157.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 157 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 157 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel157

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel158
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (30788255336518609993/5000000000000000000)
  centralHi := (615765106730372199861/100000000000000000000)
  directionLo := (617735560108224805943/100000000000000000000)
  directionHi := (77216945013528100743/12500000000000000000)

def endpointA : IntegerEndpointWitness 158 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree158.table
  base := (18879246201404650155617718717892428510059/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-11704565265258057318866757919073880000000000000)
      constant := (557673286855705885614166660581935764878671455328) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 158 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree158.table
  base := (15103396961123564103945842664750031498643/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2669182789372108248748816106760000000000000)
      constant := (128089952055937788247883738763745005669755740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 158 interval.damping) (curvature.centralUpper 158 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree158.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 158 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 158 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel158

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel159
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (617735560108224805943/100000000000000000000)
  centralHi := (77216945013528100743/12500000000000000000)
  directionLo := (61969974808594022679/10000000000000000000)
  directionHi := (619699748085940226791/100000000000000000000)

def endpointA : IntegerEndpointWitness 159 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree159.table
  base := (77009817569986507421669500547439088116191/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-3925736289565643473985501205643380000000000000)
      constant := (188235842257052201308024348626044909445567982056) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 159 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree159.table
  base := (1203278399531029050306945793809259336907/156250000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-895250444893633160470258762260000000000000)
      constant := (43235183273879054965236857102603011170744576) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 159 interval.damping) (curvature.centralUpper 159 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree159.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 159 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 159 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel159

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel160
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (61969974808594022679/10000000000000000000)
  centralHi := (619699748085940226791/100000000000000000000)
  directionLo := (24866309202077684559/4000000000000000000)
  directionHi := (77707216256492764247/12500000000000000000)

def endpointA : IntegerEndpointWitness 160 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree160.table
  base := (19628939439867834523452702519242255214397/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-11849852472135803525046249314786400000000000000)
      constant := (571785904829908368508362229741617768829357656224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 160 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree160.table
  base := (1570315155189415990235163517314306555223/200000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2702319879989690714072736466800000000000000)
      constant := (131331284439404211553242687083165751799401400) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 160 interval.damping) (curvature.centralUpper 160 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree160.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 160 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 160 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel160

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel161
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (24866309202077684559/4000000000000000000)
  centralHi := (77707216256492764247/12500000000000000000)
  directionLo := (623609564462323564263/100000000000000000000)
  directionHi := (77951195557790445533/12500000000000000000)

def endpointA : IntegerEndpointWitness 161 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree161.table
  base := (80034805369949340656034241784156513909171/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-11922496075574676628135995012642660000000000000)
      constant := (578908421031305304861664205558939961474225829208) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 161 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree161.table
  base := (40017402684974446586538497022659543874717/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2718888425298481946734696646820000000000000)
      constant := (132967155909090473284452332529103987158979624) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 161 interval.damping) (curvature.centralUpper 161 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree161.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 161 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 161 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel161

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel162
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (623609564462323564263/100000000000000000000)
  centralHi := (77951195557790445533/12500000000000000000)
  directionLo := (625555308861210484447/100000000000000000000)
  directionHi := (19548603401912827639/3125000000000000000)

def endpointA : IntegerEndpointWitness 162 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree162.table
  base := (81566960397358274657891529668508685117721/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-3998379893004516577075246903499640000000000000)
      constant := (195358358458233773921605359173084971450201096536) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 162 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree162.table
  base := (81566960397357902879229139973670847656541/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-911818990202424393132218942280000000000000)
      constant := (44871054743516569848554040404114050171878492) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 162 interval.damping) (curvature.centralUpper 162 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree162.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 162 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 162 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel162

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel163
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (625555308861210484447/100000000000000000000)
  centralHi := (19548603401912827639/3125000000000000000)
  directionLo := (627495019900556660983/100000000000000000000)
  directionHi := (78436877487569582623/12500000000000000000)

def endpointA : IntegerEndpointWitness 163 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree163.table
  base := (83112222837696137443951634875729153202169/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-12067783282452422834315486408355180000000000000)
      constant := (593285867859459908699476849754864496608498575112) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 163 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree163.table
  base := (8311222283769582857378207678597393265513/1000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2752025515916064412058617006860000000000000)
      constant := (136269309403637848334840481805747561575584680) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 163 interval.damping) (curvature.centralUpper 163 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree163.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 163 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 163 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel163

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel164
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (627495019900556660983/100000000000000000000)
  centralHi := (78436877487569582623/12500000000000000000)
  directionLo := (314714376679694899649/50000000000000000000)
  directionHi := (629428753359389799299/100000000000000000000)

def endpointA : IntegerEndpointWitness 164 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree164.table
  base := (84670592687019924091608887043670131730551/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-12140426885891295937405232106211440000000000000)
      constant := (600540798484953938618715935606009827111480675448) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 164 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree164.table
  base := (84670592687019667494818475013283241688461/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2768594061224855644720577186880000000000000)
      constant := (137935591428212941552558390448438196700784596) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 164 interval.damping) (curvature.centralUpper 164 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree164.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 164 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 164 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel164

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel165
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (314714376679694899649/50000000000000000000)
  centralHi := (629428753359389799299/100000000000000000000)
  directionLo := (631356564162527030513/100000000000000000000)
  directionHi := (315678282081263515257/50000000000000000000)

def endpointA : IntegerEndpointWitness 165 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree165.table
  base := (21560517485361104983781570481398107024441/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-4071023496443389680164992601355900000000000000)
      constant := (202613289083521825300125732007085176918031056224) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 165 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree165.table
  base := (5390129371340262923300981146211313868417/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-928387535511215625794179122300000000000000)
      constant := (46537336768045040511837677411010072262736064) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 165 interval.damping) (curvature.centralUpper 165 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree165.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 165 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 165 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel165

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel166
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (631356564162527030513/100000000000000000000)
  centralHi := (315678282081263515257/50000000000000000000)
  directionLo := (633278506398777651319/100000000000000000000)
  directionHi := (15831962659969441283/2500000000000000000)

def endpointA : IntegerEndpointWitness 166 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree166.table
  base := (21956663649285256157476186336060381352171/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-12285714092769042143584723501923960000000000000)
      constant := (615183074155685589316852837450857631133200372832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 166 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree166.table
  base := (21956663649285211889082006143932943483663/2500000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2801731151842438110044497546920000000000000)
      constant := (141298566031266558725052361160736343861647472) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 166 interval.damping) (curvature.centralUpper 166 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree166.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 166 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 166 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel166

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel167
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (633278506398777651319/100000000000000000000)
  centralHi := (15831962659969441283/2500000000000000000)
  directionLo := (158798658334662540967/25000000000000000000)
  directionHi := (635194633338650163869/100000000000000000000)

def endpointA : IntegerEndpointWitness 167 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree167.table
  base := (89424346650336606751711016470738853662809/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-12358357696207915246674469199780220000000000000)
      constant := (622570419199714169861381408226504649447362445832) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 167 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree167.table
  base := (5589021665646028728893238427863149685923/625000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2818299697151229342706457726940000000000000)
      constant := (142995258609471420434586086232001674219091648) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 167 interval.damping) (curvature.centralUpper 167 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree167.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 167 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 167 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel167

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel168
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (158798658334662540967/25000000000000000000)
  centralHi := (635194633338650163869/100000000000000000000)
  directionLo := (63710499745158001529/10000000000000000000)
  directionHi := (637104997451580015291/100000000000000000000)

def endpointA : IntegerEndpointWitness 168 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree168.table
  base := (91035146097312387964305559917148564890091/10000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 530160000000000000000000000000000000000000000
      center := (1442477)
      previous := (0)
      next := (1049275)
      square := (20914238049782761685868592950960000000000000)
      linear := (-4143667099882262783254738299212160000000000000)
      constant := (210000634127353251092380227574605388316213064456) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 168 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree168.table
  base := (45517573048656132893066150442446760266263/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 120000000000000000000000000000000000000000
      center := (329)
      previous := (0)
      next := (235)
      square := (4733870088226066474845765720000000000000)
      linear := (-944956080820006858456139302320000000000000)
      constant := (48234029346205276893716505263098722246390312) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 168 interval.damping) (curvature.centralUpper 168 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree168.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 168 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 168 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel168

namespace ForestUnimodality.Stage130KernelData.Cell225.Kernel169
open FiniteKernelRationalCertificate FiniteKernelCurvatureCertificate BinomialMassIntervalCertificate
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def curvature : DegreeWitness where
  centralLo := (63710499745158001529/10000000000000000000)
  centralHi := (637104997451580015291/100000000000000000000)
  directionLo := (639009650422693799033/100000000000000000000)
  directionHi := (319504825211346899517/50000000000000000000)

def endpointA : IntegerEndpointWitness 169 where
  qNumerator := 653
  qDenominator := 1128
  table := BinomialMassData.Q653_1128.Degree169.table
  base := (46329526467201427912860904639611708873543/5000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 1590480000000000000000000000000000000000000000
      center := (4327431)
      previous := (0)
      next := (3147825)
      square := (62742714149348285057605778852880000000000000)
      linear := (-12503644903085661452853960595492740000000000000)
      constant := (637477523702139347141260762489329462395838534128) }

theorem endpointA_checked : endpointA.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q653_1128.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointA.polynomial).streamCheck_sound endpointA.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel


def endpointB : IntegerEndpointWitness 169 where
  qNumerator := 7
  qDenominator := 12
  table := BinomialMassData.Q7_12.Degree169.table
  base := (18531810586880550868673789447007817832793/2000000000000000000000000000000000000000)
  polynomial :=
    { denominator := 360000000000000000000000000000000000000000
      center := (987)
      previous := (0)
      next := (705)
      square := (14201610264678199424537297160000000000000)
      linear := (-2851436787768811808030378086980000000000000)
      constant := (146419054318567831047701350556133907209902740) }

theorem endpointB_checked : endpointB.check row interval.lo interval.hi
    (curvature.directionUpper 169 interval.damping) (curvature.centralUpper 169 interval.damping) = true := by
  simp only [IntegerEndpointWitness.check, Bool.and_eq_true_iff, and_assoc]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact BinomialMassData.Q7_12.Degree169.checked
  · decide +kernel
  · decide +kernel
  · apply (endpointB.polynomial).streamCheck_sound endpointB.table (by decide +kernel) (by decide +kernel)
    decide +kernel
  · decide +kernel
  · decide +kernel

def witness : IntegerDegreeWitness 169 := ⟨curvature,endpointA,endpointB⟩

theorem checked : witness.check row interval = true := by
  simp only [IntegerDegreeWitness.check, Bool.and_eq_true_iff, and_assoc]
  exact ⟨by decide +kernel, by decide +kernel, endpointA_checked, endpointB_checked⟩

theorem actual_residual_nonneg (j : ℤ) {q : ℝ}
    (hq : q ∈ Set.Icc (interval.lo : ℝ) (interval.hi : ℝ)) :
    0 ≤ row.toReal.residual 169 j q :=
  witness.check_sound row interval row_checked interval_checked checked j hq

#print axioms checked
#print axioms actual_residual_nonneg
end ForestUnimodality.Stage130KernelData.Cell225.Kernel169
