\name{scrp}
\alias{scrp}
\title{ Successive Constant Rebalanced Portfolio }
\description{
  Take the weights for the best CRP in the past as the weights for the
  next period.
}
\usage{
scrp(x, from = 1, by = 1, fast.only = TRUE)
}
%- maybe also 'usage' for other objects documented here.
\arguments{
  \item{x}{
    Time series of relative prices
}
  \item{from}{
    Start time 
}
  \item{by}{
    Step in time to recalculate best CRP
}
  \item{fast.only}{
  Only use the fast but slightly inaccurate version of CRP optimization.
}
}
\details{
  At each time index ti = from + i * by, calculate the weights for the best CRP up to
  but not including ti, and uses that as portfolio until the next
  optimization point.  Return the time series of the corresponding
  portfolio wealth.
}
\value{
  Return the time series of portfolio wealths.
}
\references{
  Gaivoronski, A and Stella, F (2000): Nonstationary Optimization Approach for Finding Universal Portfolios. Published in: Annals of Operations Research , Vol. 100, (2000): pp. 165-188.
}
\author{ Marc Delvaux }
