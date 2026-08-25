import Ragu.Meta.EndpointCensus
import Ragu.Fingerprint.Main

/-! The exact-fingerprint executable has a root-level `main`. Keep its
computability check in a module that imports only this executable, because the
polynomial-fingerprint executable defines a distinct root-level `main`. -/

census_computable _root_.main +choice
