\name{wscrp}
\alias{wscrp}
%- Also NEED an '\alias' for EACH other topic documented here.
\title{ Weighted Successive Constant Rebalanced Portfolio }
\description{
  Calculate current portfolio weights as a weighted average of the best
  CRP until now and the previous weights
}
\usage{
wscrp(x, k0 = 1, k = 1, a = 0.99, fast.only = TRUE)
}
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
  \item{a}{
    The weight between old and new
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
