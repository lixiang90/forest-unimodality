import ForestUnimodality.NonnegativeSourceCells
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace ForestUnimodality.NonnegativeSourceData.Case13
open NonnegativeSource
def parameters : Parameters :=
  ⟨(6/5),
  (99/200),
  (454729/1000000),
  (945027/1000000),
  (160263/500000),
  ⟨2, (660263/1000000), 16, (1935301251705671111/1000000000000000000), (387060250341134249/200000000000000000)⟩,
  (3745390934853537369323691438899974321/1000000000000000000000000000000000000),
  (149815637394141515519377075840794001/40000000000000000000000000000000000)⟩
theorem parameters_checked : parameters.check=true := by decide +kernel
#print axioms parameters_checked
end ForestUnimodality.NonnegativeSourceData.Case13
