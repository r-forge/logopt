\name{scrp}
\alias{scrp}
\title{ Successive Constant Rebalanced Portfolio }
\description{
  Take the weights for the best CRP in the past as the weights for the
  next period.
}
\usage{
scrp(x, k0 = 1, k = 1, fast.only = TRUE)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{x}{
    Time series of relative prices
}
  \item{k0}{
    Start time 
}
  \item{k}{
    Step in time to recalculate best CRP
}
  \item{fast.only}{
  Only use the fast but slightly inaccurate version of CRP optimization
}
}
\details{
  TBD
}
\value{
  Return the time series of portfolio wealths.
}
\references{
  Gaivoronski, A and Stella, F (2000): Nonstationary Optimization Approach for Finding Universal Portfolios. Published in: Annals of Operations Research , Vol. 100, (2000): pp. 165-188.
}
\author{ Marc Delvaux }
