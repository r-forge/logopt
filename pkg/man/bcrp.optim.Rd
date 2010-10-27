\name{bcrp.optim}
\alias{bcrp.optim}
\title{ Find the best constant rebalanced portfolio }
\description{
  Optimize a vector of portfolio weights, constant in time, that results
  in the best terminal wealth.
}
\usage{
bcrp.optim(x, maxit = 20, clean.up = TRUE, clean.up.eps = 1e-10, fast.only = FALSE)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{x}{
    Time series of relative prices
}
\item{maxit}{
  Maximum number of iterations, passed to optim
}
\item{clean.up}{
  Typically some portfolio components are zero, but the optimization
  procedure stops with very small value.  If clean.up is true, very
  small values are forced to zero.
}
\item{clean.up.eps}{
  If clean.up is true, the values less than clean.up.eps are forced to zero.
}
\item{fast.only}{
    Only use the fast but slightly inaccurate version of CRP
    optimization.  The fast algorithm uses a quadratic approximation of
    the loss function so that quadprod can be used for an algebraic solution.
}
}
\details{
  TBD
}
\value{
  The optimal set of portfolio weights.
}
\references{
  TBD, the article that introduced the quadratic approximation (Gyorfi
  log-optimal site)
}
\author{ Marc Delvaux }
