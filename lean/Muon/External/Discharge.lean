import Muon.External.Certificates
import GaussianFoundations.OpNorm
import GaussianFoundations.QuadFormLp
import GaussianFoundations.Poincare

/-!
# Foundation proofs for the Gaussian interfaces

The consuming theorems retain explicit interface arguments. These proofs supply all four
interfaces from the accompanying `gaussian_foundations` dependency.
-/

namespace Muon.External

theorem gaussianOpNorm : GaussianOpNorm :=
  ⟨GaussianFoundations.gaussianOpNorm⟩

theorem gaussianOpNormL6 : GaussianOpNormL6 :=
  ⟨GaussianFoundations.gaussianOpNormL6⟩

theorem gaussianQuadFormLp : GaussianQuadFormLp :=
  ⟨GaussianFoundations.gaussianQuadFormLp⟩

theorem gaussianPoincare : GaussianPoincare :=
  ⟨GaussianFoundations.gaussianPoincare⟩

end Muon.External
