\name{nn.gyorfi}
\alias{nn.gyorfi}
\title{ Portfolio selection using nearest neighbor }
\description{
  Implement the portfolio selction defined by Gyorfi.  At each instant
  in time, look back for a set of nearest neighbors, then find the best
  CRP for the time steps following the nearest neighbors and use the
  corresponding weights for the next time step.  This is done for a set
  of parameters, defining so-called experts.  The final performance is
  the (weighted) average across all experts.
}
\usage{
nn.gyorfi(x, pls, ks, qkl=NULL)
}
\arguments{
  \item{x}{
    Time series of relative prices
}
\item{pls}{
  pls is either a scalar or a sequence.  If its a scalar, it is the
  value L as defined in Gyorfi article, and the pl sequence is 0.02 +
  0.05 * (l-1)/(L-1), l in 1:L.  Otherwise pls is the sequence of pl
  values itself.  
}
\item{ks}{
  ks is either a scalar or a sequence.  If its a scalar, it is the
  value K as defined in Gyorfi article, and the k sequence is 1:K.
  Otherwise ks is the sequence of k values itself.
}
\item{qkl}{
  A priori weights for the experts, this is a matrix (K,L) that should
  sum to 1.  The NULL default results in an uniform loading.
}
}
\details{
  Straightforward implementation of the nearest neighbors portfolio
  algorithm.  
}
\value{
  Return a list containing in order the set of weights and wealth
  evolution corresponding to all combinations of pl and k values.
}
\references{
  L. Gyorfi, F. Udina and H. Walk, "Nonparametric nearest neighbor based
  empirical portfolio selection strategies", Statistics & Decisions, 26:145-157, 2008.
}
\author{ Marc Delvaux
}

